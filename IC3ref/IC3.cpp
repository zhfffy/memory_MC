/*********************************************************************
Copyright (c) 2013, Aaron Bradley

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#include <algorithm>
#include <iostream>
#include <set>
#include <sys/times.h>

#include "IC3.h"
#include "Solver.h"
#include "Vec.h"

// A reference implementation of IC3, i.e., one that is meant to be
// read and used as a starting point for tuning, extending, and
// experimenting.
//
// High-level details:
//
//  o The overall structure described in
//
//      Aaron R. Bradley, "SAT-Based Model Checking without
//      Unrolling," VMCAI'11
//
//    including frames, a priority queue of frame-specific proof
//    obligations, and induction-based generalization.  See check(),
//    strengthen(), handleObligations(), mic(), propagate().
//
//  o Lifting, inspired by
//
//      Niklas Een, Alan Mishchenko, Robert Brayton, "Efficient
//      Implementation of Property Directed Reachability," FMCAD'11
//
//    Each CTI is lifted to a larger cube whose states all have the
//    same successor.  The implementation is based on
//
//      H. Chockler, A. Ivrii, A. Matsliah, S. Moran, and Z. Nevo,
//      "Incremental Formal Veriﬁcation of Hardware," FMCAD'11.
//
//    In particular, if s with inputs i is a predecessor of t, then s
//    & i & T & ~t' is unsatisfiable, where T is the transition
//    relation.  The unsat core reveals a suitable lifting of s.  See
//    stateOf().
//
//  o One solver per frame, which various authors of IC3
//    implementations have tried (including me in pre-publication
//    work, at which time I thought that moving to one solver was
//    better).
//
//  o A straightforward proof obligation scheme, inspired by the ABC
//    implementation.  I have so far favored generalizing relative to
//    the maximum possible level in order to avoid over-strengthening,
//    but doing so requires a more complicated generalization scheme.
//    Experiments by Zyad Hassan indicate that generalizing relative
//    to earlier levels works about as well.  Because literals seem to
//    be dropped more quickly, an implementation of the "up" algorithm
//    (described in my FMCAD'07 paper) is unnecessary.
//
//    The scheme is as follows.  For obligation <s, i>:
//
//    1. Check consecution of ~s relative to i-1.
//
//    2. If it succeeds, generalize, then push foward to, say, j.  If
//       j <= k (the frontier), enqueue obligation <s, j>.
//
//    3. If it fails, extract the predecessor t (using stateOf()) and
//       enqueue obligation <t, i-1>.
//
//    The upshot for this reference implementation is that it is
//    short, simple, and effective.  See handleObligations() and
//    generalize().
//
//  o The generalization method described in
//
//      Zyad Hassan, Aaron R. Bradley, and Fabio Somenzi, "Better
//      Generalization in IC3," (submitted May 2013)
//
//    which seems to be superior to the single-clause method described
//    in the original paper, first described in
//
//      Aaron R. Bradley and Zohar Manna, "Checking Safety by
//      Inductive Generalization of Counterexamples to Induction,"
//      FMCAD'07
//
//    The main idea is to address not only CTIs, which are states
//    discovered through IC3's explict backward search, but also
//    counterexamples to generalization (CTGs), which are states that
//    are counterexamples to induction during generalization.  See
//    mic() and ctgDown().
//
//    A basic one-cube generalization scheme can be used instead
//    (third argument of check()).
//
// Limitations in roughly descending order of significance:
//
//  o A permanent limitation is that there is absolutely no
//    simplification of the AIGER spec.  Use, e.g.,
//
//      iimc -t pp -t print_aiger 
//
//    or ABC's simplification methods to produce preprocessed AIGER
//    benchmarks.  This implementation is intentionally being kept
//    small and simple.
//
//  o An implementation of "up" is not provided, as it seems that it's
//    unnecessary when both lifting-based and unsat core-based
//    reduction are applied to a state, followed by mic before
//    pushing.  The resulting cube is sufficiently small.

namespace IC3 {

  class IC3 {
  public:
    IC3(Model & _model) :
      verbose(0), random(false), model(_model), k(1), nextState(0),
      litOrder(), slimLitOrder(),
      numLits(0), numUpdates(0), maxDepth(1), maxCTGs(3),
      maxJoins(1<<20), micAttempts(3), cexState(0), nQuery(0), nCTI(0), nCTG(0),
      nmic(0), satTime(0), nCoreReduced(0), nAbortJoin(0), nAbortMic(0)
    {
      slimLitOrder.heuristicLitOrder = &litOrder;

      // construct lifting solver
      lifts = model.newSolver();
      // don't assert primed invariant constraints
      model.loadTransitionRelation(*lifts, false);
      // assert notInvConstraints (in stateOf) when lifting
      notInvConstraints = Minisat::mkLit(lifts->newVar());
      Minisat::vec<Minisat::Lit> cls;
      cls.push(~notInvConstraints);
      for (LitVec::const_iterator i = model.invariantConstraints().begin();
           i != model.invariantConstraints().end(); ++i)
        cls.push(model.primeLit(~*i));
      lifts->addClause_(cls);
    }
    ~IC3() {
      for (vector<Frame>::const_iterator i = frames.begin(); 
           i != frames.end(); ++i)
        if (i->consecution) delete i->consecution;
      delete lifts;
    }

    // The main loop.
    bool check() {
      startTime = time();  // stats
      while (true) {
        if (verbose > 1) cout << endl << endl <<"-----------------Add Level " << k << "-----------------"<< endl;
        extend();                         // push frontier frame
        if (!strengthen()) return false;  // strengthen to remove bad successors
        if (propagate()) return true;     // propagate clauses; check for proof
        printStats();
        ++k;                              // increment frontier
      }
    }

    // Follows and prints chain of states from cexState forward.
   void printWitness() {
      if (cexState != 0) {
        size_t curr = cexState;
        while (curr) {
          cout << stringOfLitVec(state(curr).inputs) 
               << stringOfLitVec(state(curr).latches) << endl;
          curr = state(curr).successor;
        }
      }
    }

  private:

    int verbose; // 0: silent, 1: stats, 2: all
    bool random;

    string stringOfLitVec(const LitVec & vec) {
      stringstream ss;
      for (LitVec::const_iterator i = vec.begin(); i != vec.end(); ++i)
        ss << model.stringOfLit(*i) << " ";
      return ss.str();
    }

    //--------------------------------------print CubeSet-----------------------------------------
    void PrintCubesetOfFrame(size_t frame_index){
        cout << "CubeSet of frame " << frame_index << ": " << endl;
      	for(CubeSet::iterator m=frames[frame_index].borderCubes.begin(); m!=frames[frame_index].borderCubes.end(); m++){
            cout << stringOfLitVec(*m) << endl;	 
      	}
    }

    Model & model;
    size_t k;

    // 定义states是存储state的数据结构 每个state存储一组对literal的赋值
    // The State structures are for tracking trees of (lifted) CTIs.
    // Because States are created frequently, I want to avoid dynamic
    // memory management; instead their (de)allocation is handled via
    // a vector-based pool.
    struct State {
      size_t successor;  // successor State
      LitVec latches;
      LitVec inputs;
      size_t index;      // for pool
      bool used;         // for pool
    };
    vector<State> states; 
    size_t nextState;
    // WARNING: do not keep reference across newState() calls
    State & state(size_t sti) { return states[sti-1]; }
    size_t newState() {
      if (nextState >= states.size()) {
        states.resize(states.size()+1);
        states.back().index = states.size();
        states.back().used = false;
      }
      size_t ns = nextState;
      assert (!states[ns].used);
      states[ns].used = true;
      while (nextState < states.size() && states[nextState].used)
        nextState++;
      return ns+1;
    }
    void delState(size_t sti) {
      State & st = state(sti);
      st.used = false;
      st.latches.clear();
      st.inputs.clear();
      if (nextState > st.index-1) nextState = st.index-1;
    }
    void resetStates() {
      for (vector<State>::iterator i = states.begin(); i != states.end(); ++i) {
        i->used = false;
        i->latches.clear();
        i->inputs.clear();
      }
      nextState = 0;
    }

    // 定义存储大量LitVec的集合CubeSet 集合中的LitVec有序排列
    // A CubeSet is a set of ordered (by integer value) vectors of
    // Minisat::Lits.
    static bool _LitVecComp(const LitVec & v1, const LitVec & v2) { //定义两个LitVec的排序关系
      if (v1.size() < v2.size()) return true;
      if (v1.size() > v2.size()) return false;
      for (size_t i = 0; i < v1.size(); ++i) {
        if (v1[i] < v2[i]) return true;
        if (v2[i] < v1[i]) return false;
      }
      return false;
    }
    static bool _LitVecEq(const LitVec & v1, const LitVec & v2) {  //定义两个LitVec的等价关系
      if (v1.size() != v2.size()) return false;
      for (size_t i = 0; i < v1.size(); ++i)
        if (v1[i] != v2[i]) return false;
      return true;
    }
    class LitVecComp {
    public:
      bool operator()(const LitVec & v1, const LitVec & v2) {
        return _LitVecComp(v1, v2);
      }
    };
    typedef set<LitVec, LitVecComp> CubeSet;

    // 定义证明义务 将 第st个state 从 frame Fl 中删除 深度为d/d步转移后到达error
    struct Obligation {
      Obligation(size_t st, size_t l, size_t d) :
        state(st), level(l), depth(d) {}
      size_t state;  // Generalize this state...
      size_t level;  // ... relative to this level.
      size_t depth;  // Length of CTI suffix to error.
    };
    class ObligationComp {
    public:
      bool operator()(const Obligation & o1, const Obligation & o2) {
        if (o1.level < o2.level) return true;  // prefer lower levels (required)
        if (o1.level > o2.level) return false;
        if (o1.depth < o2.depth) return true;  // prefer shallower (heuristic)
        if (o1.depth > o2.depth) return false;
        if (o1.state < o2.state) return true;  // canonical final decider
        return false;
      }
    };
    typedef set<Obligation, ObligationComp> PriorityQueue;


    // 定义frame Fk的帧序号为k borderCubes表示这一帧不包含的state的集合(显然previous frame也不包含这样的state)
    // For IC3's overall frame structure.
    struct Frame {
      size_t k;             // steps from initial state
      CubeSet borderCubes;  // additional cubes in this and previous frames
      Minisat::Solver * consecution;
    };
    vector<Frame> frames;

    Minisat::Solver * lifts;
    Minisat::Lit notInvConstraints;

    // Push a new Frame.
    void extend() {
      while (frames.size() < k+2) {
        frames.resize(frames.size()+1);
        Frame & fr = frames.back();
        fr.k = frames.size()-1;
        fr.consecution = model.newSolver();
        if (random) {
          fr.consecution->random_seed = rand();
          fr.consecution->rnd_init_act = true;
        }
        if (fr.k == 0) model.loadInitialCondition(*fr.consecution);
        model.loadTransitionRelation(*fr.consecution);
        cout << "frames.size = " << frames.size() << "   fr.k = " << fr.k << endl;
      }
    }

    // 启发式算法 决定litVec中哪个literal先被drop
    // Structure and methods for imposing priorities on literals
    // through ordering the dropping of literals in mic (drop leftmost
    // literal first) and assumptions to Minisat.  The implemented
    // ordering prefers to keep literals that appear frequently in
    // addCube() calls.
    struct HeuristicLitOrder {
      HeuristicLitOrder() : _mini(1<<20) {}
      vector<float> counts;
      size_t _mini;
      void count(const LitVec & cube) {
        assert (!cube.empty());
        // assumes cube is ordered
        size_t sz = (size_t) Minisat::toInt(Minisat::var(cube.back()));
        if (sz >= counts.size()) counts.resize(sz+1);
        _mini = (size_t) Minisat::toInt(Minisat::var(cube[0]));
        for (LitVec::const_iterator i = cube.begin(); i != cube.end(); ++i)
          counts[(size_t) Minisat::toInt(Minisat::var(*i))] += 1;
      }
      void decay() {
        for (size_t i = _mini; i < counts.size(); ++i)
          counts[i] *= 0.99;
      }
    } litOrder;

    struct SlimLitOrder {
      HeuristicLitOrder *heuristicLitOrder;

      SlimLitOrder() {}

      bool operator()(const Minisat::Lit & l1, const Minisat::Lit & l2) const {
        // l1, l2 must be unprimed
        size_t i2 = (size_t) Minisat::toInt(Minisat::var(l2));
        if (i2 >= heuristicLitOrder->counts.size()) return false;
        size_t i1 = (size_t) Minisat::toInt(Minisat::var(l1));
        if (i1 >= heuristicLitOrder->counts.size()) return true;
        return (heuristicLitOrder->counts[i1] < heuristicLitOrder->counts[i2]);
      }
    } slimLitOrder;

    float numLits, numUpdates;
    void updateLitOrder(const LitVec & cube, size_t level) {
      litOrder.decay();
      numUpdates += 1;
      numLits += cube.size();
      litOrder.count(cube);
    }

    // order according to preference
    void orderCube(LitVec & cube) {
      stable_sort(cube.begin(), cube.end(), slimLitOrder);
    }

    typedef Minisat::vec<Minisat::Lit> MSLitVec;

    // Orders assumptions for Minisat.
    void orderAssumps(MSLitVec & cube, bool rev, int start = 0) {
      stable_sort(cube + start, cube + cube.size(), slimLitOrder);
      if (rev) reverse(cube + start, cube + cube.size());
    }

    // SAT有解 ，即至少有一组变量赋值满足SAT，扩大这个解(lift) 
    // 输入frame index和next state index(latch'), succ = 0表示next state是error
    // Assumes that last call to fr.consecution->solve() was satisfiable.  
    // Extracts state(s) cube from satisfying assignment.
    size_t stateOf(Frame & fr, size_t succ = 0) {
      // create state
      size_t st = newState();
      state(st).successor = succ;
      MSLitVec assumps;
      assumps.capacity(1 + 2 * (model.endInputs()-model.beginInputs())
                       + (model.endLatches()-model.beginLatches()));
      Minisat::Lit act = Minisat::mkLit(lifts->newVar());  // activation literal
      assumps.push(act);
      Minisat::vec<Minisat::Lit> cls;
      cls.push(~act);
      cls.push(notInvConstraints);  // successor must satisfy inv. constraint
      if (succ == 0)         //lift CTI  input i & state s & T & ~error' 不可满足
        cls.push(~model.primedError());
      //F & !s & T & s'有解t, state t导致~s相对归纳失败, 需要lift t
      //aiger模型中state(succ)表示要被删除的状态s，包含input和latch
      //上式即F & !latch & T & latch'有解input0 latch0 input0'代入得(input0&latch0) & T & (input0'&latch')为真
      //所以input0 & latch0 & T & input0' & ~latch‘为假 UNSAT
      else                   
        for (LitVec::const_iterator i = state(succ).latches.begin(); 
             i != state(succ).latches.end(); ++i)
          cls.push(model.primeLit(~*i));                           //求解器lift中加入子句~latch'
      lifts->addClause_(cls);                                            
      // extract and assert primary inputs
      for (VarVec::const_iterator i = model.beginInputs(); 
           i != model.endInputs(); ++i) {
        Minisat::lbool val = fr.consecution->modelValue(i->var());
        if (val != Minisat::l_Undef) {
          Minisat::Lit pi = i->lit(val == Minisat::l_False);
          state(st).inputs.push_back(pi);  // record full inputs，  赋值数组加入input0的赋值
          assumps.push(pi);                    
        }
      }
      // some properties include inputs, so assert primed inputs after        
      for (VarVec::const_iterator i = model.beginInputs(); 
           i != model.endInputs(); ++i) {
        Minisat::lbool pval = 
          fr.consecution->modelValue(model.primeVar(*i).var());     //赋值数组加入input0'的赋值
        if (pval != Minisat::l_Undef)
          assumps.push(model.primeLit(i->lit(pval == Minisat::l_False)));
      }
      int sz = assumps.size();
      // extract and assert latches
      LitVec latches;
      for (VarVec::const_iterator i = model.beginLatches(); 
           i != model.endLatches(); ++i) {
        Minisat::lbool val = fr.consecution->modelValue(i->var());
        if (val != Minisat::l_Undef) {
          Minisat::Lit la = i->lit(val == Minisat::l_False);
          latches.push_back(la);
          assumps.push(la);                                       //赋值数组加入latch0的赋值
        }
      }
      orderAssumps(assumps, false, sz);  // empirically found to be best choice
      // State s, inputs i, transition relation T, successor t:
      //   s & i & T & ~t' is unsat
      // Core assumptions reveal a lifting of s.     
      ++nQuery; startTimer();  // stats
      bool rv = lifts->solve(assumps);                           //求解"赋值数组&求解器的子句"是否可满足
      endTimer(satTime);
      assert (!rv);
      // obtain lifted latch set from unsat core, lift latch0得到latch1 latch1包含的literal一定<=latch0
      for (LitVec::const_iterator i = latches.begin(); i != latches.end(); ++i)
        if (lifts->conflict.has(~*i))
          state(st).latches.push_back(*i);  // record lifted latches
      // deactivate negation of successor
      lifts->releaseVar(~act);

      //cout <<"Lifting: " <<stringOfLitVec(state(st).inputs) << stringOfLitVec(state(st).latches) << endl;
      return st;
    }

    // Checks if cube contains any initial states.
    bool initiation(const LitVec & latches) {
      return !model.isInitial(latches);
    }

    // 求解F & !s & T & s' 在aiger中求解 F & !latch & T & &latch'
    // 输入frame index, latches代表input和latch的变量数组，state(succ)存储latches
    // Check if ~latches is inductive relative to frame fi.  If it's
    // inductive and core is provided, extracts the unsat core.  If
    // it's not inductive and pred is provided, extracts
    // predecessor(s).
    bool consecution(size_t fi, const LitVec & latches, size_t succ = 0,
                     LitVec * core = NULL, size_t * pred = NULL, 
                     bool orderedCore = false)
    {
      Frame & fr = frames[fi];
      MSLitVec assumps, cls;
      assumps.capacity(1 + latches.size());
      cls.capacity(1 + latches.size());
      Minisat::Lit act = Minisat::mkLit(fr.consecution->newVar());
      assumps.push(act);
      cls.push(~act);
      for (LitVec::const_iterator i = latches.begin(); 
           i != latches.end(); ++i) {
        cls.push(~*i);                              //子句!latches存储在cls中
        assumps.push(*i);                           // push unprimed... 
      }
      // ... order... (empirically found to best choice)
      if (pred) orderAssumps(assumps, false, 1);
      else orderAssumps(assumps, orderedCore, 1);
      // ... now prime
      for (int i = 1; i < assumps.size(); ++i)
        assumps[i] = model.primeLit(assumps[i]);   //赋值数组assumps中加入latches'
      fr.consecution->addClause_(cls);             //求解器fr.consecution加入子句!latches
      // F_fi & ~latches & T & latches'
      ++nQuery; startTimer();  // stats
      bool rv = fr.consecution->solve(assumps);   
      endTimer(satTime);
      if (rv) {                           //!latch相对Fi不归纳 那么Fi中存在t = input0 & latch0 -> latches (t满足F_i & ~latches)
        // fails: extract predecessor(s)
        if (pred) *pred = stateOf(fr, succ); //被lift的t 存储在 pred指针指向的state中
        fr.consecution->releaseVar(~act);
        return false;
      }
      // succeeds                                 //!latches相对Fi归纳 那么!latches可以删除, 再lift latches
      if (core) {
        if (pred && orderedCore) {
          // redo with correctly ordered assumps 再求解一次？
          reverse(assumps+1, assumps+assumps.size());
          ++nQuery; startTimer();  // stats
          rv = fr.consecution->solve(assumps);
          assert (!rv);
          endTimer(satTime);
        }
        for (LitVec::const_iterator i = latches.begin(); 
             i != latches.end(); ++i)
          if (fr.consecution->conflict.has(~model.primeLit(*i)))
            core->push_back(*i);
        if (!initiation(*core))
          *core = latches;
      }
      fr.consecution->releaseVar(~act);
      return true;
    }

    size_t maxDepth, maxCTGs, maxJoins, micAttempts;

    // Based on
    //
    //   Zyad Hassan, Aaron R. Bradley, and Fabio Somenzi, "Better
    //   Generalization in IC3," (submitted May 2013)
    //
    // Improves upon "down" from the original paper (and the FMCAD'07 paper) by handling CTGs.
    // 找出cube相对F_level的最大归纳子句
    bool ctgDown(size_t level, LitVec & cube, size_t keepTo, size_t recDepth) {
      size_t ctgs = 0, joins = 0;
      while (true) {
        // induction check
        if (!initiation(cube))
          return false;
        // 递归深度到达极限后，若!cube相对F_level不归纳，直接返回false; 若归纳，返回true,且cube:=cube被lift的结果core
        if (recDepth > maxDepth) {
          // quick check if recursion depth is exceeded
          LitVec core;
          bool rv = consecution(level, cube, 0, &core, NULL, true); 
          if (rv && core.size() < cube.size()) {                    
            ++nCoreReduced;  // stats
            cube = core;
          }
          return rv;
        }
        // prepare to obtain CTG
        size_t cubeState = newState();
        state(cubeState).successor = 0;
        state(cubeState).latches = cube;
        size_t ctg;
        LitVec core;
        //判断!cube是否相对F_level归纳
        //sat无解 !cube归纳，cube := cube被lift的结果core（不存在ctg）
        if (consecution(level, cube, cubeState, &core, &ctg, true)) {  
          //cout << "the new cp satisfies induction, find a stronger cube " << stringOfLitVec(core)<< endl; 
          if (core.size() < cube.size()) {
            ++nCoreReduced;  // stats
            cube = core;
          }
          // inductive, so clean up
          delState(cubeState);
          return true;
        }

        //sat有解 !cube相对F_level不归纳，说明在F_level中存在ctg会一步转移到cube(这个ctg也是被StateOf()函数lift了) 返回这个ctg的状态序号ctg core=null
        //那么尝试在F_level中删除state(ctg)，要验证state(ctg)是否相对F_level-1归纳 
        //cout << "the new cp cannot satisfy induction, find a lifted ctg. Check induction of ctg "<<stringOfLitVec(state(ctg).latches) << "in frame " << level-1 << endl;
	
        LitVec ctgCore;
        bool ret = false;
        if (ctgs < maxCTGs && level > 1 && initiation(state(ctg).latches)
            && consecution(level-1, state(ctg).latches, cubeState, &ctgCore)) {
          // CTG is inductive relative to level-1; push forward and generalize
          // !ctg相对F_level-1归纳，因此可以在F_level中删除ctg，返回ctg被lift的结果ctgCore
          ++nCTG;  // stats
          ++ctgs;
          size_t j = level;
          // QUERY: generalize then push or vice versa? 
          // ctgcore相对F_j-1归纳，将ctgcore向右push到F_j-1，在F_j-1调用MIC删除ctgcore，返回包含更多状态的ctgcore'，最后在Fj删除ctgcore'
          while (j <= k && consecution(j, ctgCore)) ++j;
          mic(j-1, ctgCore, recDepth+1);
          addCube(j, ctgCore);
        }
        else if (joins < maxJoins) {
          // ran out of CTG attempts, so join instead 无法删除ctg 采用传统的join ctg and cube方法 保留ctg & cube共享的literal
          ctgs = 0;
          ++joins;
          LitVec tmp;
          for (size_t i = 0; i < cube.size(); ++i)
            if (binary_search(state(ctg).latches.begin(), 
                              state(ctg).latches.end(), cube[i]))
              tmp.push_back(cube[i]);
            else if (i < keepTo) {
              // previously failed when this literal was dropped
              ++nAbortJoin;  // stats
              ret = true;
              break;
            }
          cube = tmp;  // enlarged cube
          //cout << "fail to remove ctg, join ctg and cube, the new cube is" << stringOfLitVec(cube) << endl;
        }
        else
          ret = true;
        // clean up
        delState(cubeState);
        delState(ctg);
        if (ret) return false;
      }
    }

    // Extracts minimal inductive (relative to level) subclause from ~cube --- at least that's where the name comes from. 
    // With ctgDown, it's not quite a MIC anymore, but what's returned is inductive relative to the possibly modifed level.
    // 寻找!cube相对F_level的最小归纳字句 MIC会返回被generalize的cube
    void mic(size_t level, LitVec & cube, size_t recDepth) {
      ++nmic;  // stats
      // try dropping each literal in turn, lit数组Litvec删去第i个litreal，得到LitVec cp
      size_t attempts = micAttempts;
      orderCube(cube);
      for (size_t i = 0; i < cube.size();) {
        LitVec cp(cube.begin(), cube.begin() + i);
        cp.insert(cp.end(), cube.begin() + i+1, cube.end());  
        //cout << "ctgDown " << "level=" << level << " cp="<<stringOfLitVec(cp)<<" recDepth=" <<recDepth<< " i="<<i<<endl;
        //检查cp是否相对F_level归纳,若归纳，ctgDown返回一个被lift的cp,cube:=cp
        if (ctgDown(level, cp, i, recDepth)) {
          //cout << "ctgDown successfully returns a stronger cube " << stringOfLitVec(cp)<< endl;              
          // maintain original order 
          LitSet lits(cp.begin(), cp.end());
          LitVec tmp;
          for (LitVec::const_iterator j = cube.begin(); j != cube.end(); ++j)
            if (lits.find(*j) != lits.end())
              tmp.push_back(*j);
          cube.swap(tmp);
          // reset attempts
          attempts = micAttempts;
        }
        //cp相对F_level不归纳,尝试移除下一个literal
        else {
          //cout << "ctgDown fails, try to remove another lit" << endl;
          if (!--attempts) {  //如果连续三次移除literal失败，则认定这个cube已经是最小归纳字句，放弃继续移除literal，返回cube
            // Limit number of attempts: if micAttempts literals in a
            // row cannot be dropped, conclude that the cube is just
            // about minimal.  Definitely improves mics/second to use
            // a low micAttempts, but does it improve overall
            // performance?
            ++nAbortMic;  // stats
            return;
          }
          ++i;
        }
      }
    }

    // wrapper to start inductive generalization
    void mic(size_t level, LitVec & cube) {
      mic(level, cube, 1);
    }

    size_t earliest;  // track earliest modified level in a major iteration

    // Adds cube to frames at and below level, unless !toAll, in which case only to level.
    // 在F_level中删除cube 等价于 在F_level的borderCubes中加入cube 并更新Fi~F_level的子句
    // 此时已经将cube右推到了最大的相对归纳的frame(cube只对于F_level-1归纳，不对F_level归纳，无法从F_level+1中删除)
    void addCube(size_t level, LitVec & cube, bool toAll = true, 
                 bool silent = false)
    {
      sort(cube.begin(), cube.end());
      pair<CubeSet::iterator, bool> rv = frames[level].borderCubes.insert(cube);
      //AddCube失败 说明borderCubes中已有cube 不需要添加
      if (!rv.second) return;                                
      //AddCube成功 则向borderCubes中加入cube, rv.first指向cube; 
      //并且将子句!cube加到F_1到F_level的求解器中, toAll=0时只加入F_level的求解器(!cube已加入previous frame时)
      if (!silent && verbose > 1) 
        cout << "Add cube in level " << level << ": " << stringOfLitVec(cube) << endl;
      earliest = min(earliest, level);
      MSLitVec cls;
      cls.capacity(cube.size());
      for (LitVec::const_iterator i = cube.begin(); i != cube.end(); ++i)
        cls.push(~*i);
      for (size_t i = toAll ? 1 : level; i <= level; ++i)
        frames[i].consecution->addClause(cls);
      if (toAll && !silent) updateLitOrder(cube, level);
    }

    // ~cube was found to be inductive relative to level; now see if we can do better. 
    size_t generalize(size_t level, LitVec cube) {
      // generalize 找cube相对F_level最小归纳子句
      mic(level, cube);
      cout << "cube is generalized to "<<stringOfLitVec(cube) << endl;
      // push       同ctgDown
      do { ++level; } while (level <= k && consecution(level, cube));
      addCube(level, cube);
      cout << "push clause to level " << level << endl;
      return level;
    }

    size_t cexState;  // beginning of counterexample trace

    // Process obligations according to priority. 处理证明义务obls(state, level, depth)
    bool handleObligations(PriorityQueue obls) {
      while (!obls.empty()) {
        cout << endl << "Remaining " << obls.size() << " Obligations"<< endl; 
        PriorityQueue::iterator obli = obls.begin();
        Obligation obl = *obli;
        LitVec core;
        size_t predi;
        cout <<"handling Obligation: cube " <<stringOfLitVec(state(obl.state).latches) <<" in frame " << obl.level << endl;
        // Is the obligation fulfilled? 若state已经相对F_level归纳，移除该obls并在F_level中generalize cube(cube是lift state的结果)
        if (consecution(obl.level, state(obl.state).latches, obl.state, 
                        &core, &predi)) {
          cout << "The obligation is fulfilled, and the cube is lifted to " << stringOfLitVec(core)<<endl << endl;
          // Yes, so generalize and possibly produce a new obligation at a higher level.
          obls.erase(obli);
          cout << "Start to Generalize cube " << stringOfLitVec(core) << "in frame " << obl.level << endl;
          size_t n = generalize(obl.level, core);
          if (n <= k) //state没有被完全删除 继续删除F_n到F_k中的state
            obls.insert(Obligation(obl.state, n, obl.depth));
        }
        else if (obl.level == 0) {
          // No, in fact an initial state is a predecessor.
          cexState = predi;
          return false;
        }
        else {
          ++nCTI;  // stats
          cout << "The obligation is not fulfilled, a new CTI found." << endl; 
          // No, so focus on predecessor. F_i中存在predi导致归纳失败，需要证明predi相对F_i-1归纳
          obls.insert(Obligation(predi, obl.level-1, obl.depth+1));
        }
      }
      return true;
    }

    bool trivial;  // indicates whether strengthening was required
                   // during major iteration

    // Strengthens frontier to remove error successors.
    bool strengthen() {
      cout << "Strengthen frames[" << k << "]" << endl;
      Frame & frontier = frames[k];
      trivial = true;  // whether any cubes are generated
      earliest = k+1;  // earliest frame with enlarged borderCubes
      while (true) {
        ++nQuery; startTimer();  // stats
        bool rv = frontier.consecution->solve(model.primedError());
        endTimer(satTime);
        if (!rv) 
	    {cout << "No CTI found." <<endl; return true;}
        cout << "CTI exists, start to handle CTI with error successor" <<endl;
        // handle CTI with error successor
        ++nCTI;  // stats
        trivial = false;
        PriorityQueue pq;
        // enqueue main obligation and handle
        pq.insert(Obligation(stateOf(frontier), k-1, 1));
        if (!handleObligations(pq)) 
          {cout << "Fail to handle Obligation" << endl; return false;}
        cout << "Handle CTI successfully" << endl;  
         
        // finished with States for this iteration, so clean up
        resetStates();
      }
    }

    // Propagates clauses forward using induction.  If any frame has
    // all of its clauses propagated forward, then two frames' clause
    // sets agree; hence those clause sets are inductive
    // strengthenings of the property.  See the four invariants of IC3
    // in the original paper.
    bool propagate() {
      //--------------------------------------print CubeSet-----------------------------------------	
      for(size_t n = 0; n < frames.size(); ++n)  PrintCubesetOfFrame(n);

      if (verbose > 1) cout << "propagate" << endl;
      // 1. clean up: remove c in frame i if c appears in frame j when i < j
      cout << "remove cube s in frame i if s appears in frame j > i" << endl;             
      CubeSet all; 
      for (size_t i = k+1; i >= earliest; --i) {
        Frame & fr = frames[i];
        CubeSet rem, nall;
        //set_difference求两个集合的差集 返回属于1不属于2的元素集
        //fr.borderCubes存储F_i的cube; all存储F_k(k>i)的所有cube
        //borderCubes和all的差集存储在rem的尾部 F_i的cubeset只需要存储这个差集rem
        set_difference(fr.borderCubes.begin(), fr.borderCubes.end(),
                       all.begin(), all.end(),
                       inserter(rem, rem.end()), LitVecComp());    //rem := borderCube(Fi) - all(Fk)
        if (verbose > 1)
          cout << "frame: " <<i << " CubeSize: " << fr.borderCubes.size() << " RemoveSize: " << rem.size() << " ";
        fr.borderCubes.swap(rem);          //borderCube := rem = borderCube - all
        set_union(rem.begin(), rem.end(),
                  all.begin(), all.end(), 
                  inserter(nall, nall.end()), LitVecComp());
        all.swap(nall);  //all := all + rem 将这一帧的cube加入all中
        for (CubeSet::const_iterator i = fr.borderCubes.begin(); 
             i != fr.borderCubes.end(); ++i)
          assert (all.find(*i) != all.end());  //显然这一帧的所有cube都已在all中
        if (verbose > 1)
          cout << "AllRemoveSize: " <<all.size() << endl;
      }
      // 2. check if each c in frame i can be pushed to frame j
      // 如果Fi中的子句!cube相对Fi归纳 就将!cube右推加入到Fi+1中; 如果!cube被lift了，就把这个字句额外加入F1~Fi+1中
      cout << "try to push cls c in frame i to frame j > i" << endl;
      for (size_t i = trivial ? k : 1; i <= k; ++i) {
        int ckeep = 0, cprop = 0, cdrop = 0;
        Frame & fr = frames[i];
        for (CubeSet::iterator j = fr.borderCubes.begin(); 
             j != fr.borderCubes.end();) {
          LitVec core;
          if (consecution(i, *j, 0, &core)) {
            ++cprop;
            // only add to frame i+1 unless the core is reduced
            addCube(i+1, core, core.size() < j->size(), true);
            CubeSet::iterator tmp = j;
            ++j;
            fr.borderCubes.erase(tmp);
          }
          else {
            ++ckeep;
            ++j;
          }
        }
        if (verbose > 1)
          cout << "frame="<<i << " ckeep=" << ckeep << " cprop=" << cprop << " cdrop=" << cdrop << endl;
        if (fr.borderCubes.empty())
          return true;
      }
      // 3. simplify frames
      for (size_t i = trivial ? k : 1; i <= k+1; ++i)
        frames[i].consecution->simplify();
      lifts->simplify();
	
      //--------------------------------------print CubeSet-----------------------------------------	
      return false;
    }

    int nQuery, nCTI, nCTG, nmic;
    clock_t startTime, satTime;
    int nCoreReduced, nAbortJoin, nAbortMic;
    clock_t time() {
      struct tms t;
      times(&t);
      return t.tms_utime;
    }
    clock_t timer;
    void startTimer() { timer = time(); }
    void endTimer(clock_t & t) { t += (time() - timer); }
    void printStats() {
      if (!verbose) return;
      clock_t etime = time();
      cout << ". Elapsed time: " << ((double) etime / sysconf(_SC_CLK_TCK)) << endl;
      etime -= startTime;
      if (!etime) etime = 1;
      cout << ". % SAT:        " << (int) (100 * (((double) satTime) / ((double) etime))) << endl;
      cout << ". K:            " << k << endl;
      cout << ". # Queries:    " << nQuery << endl;
      cout << ". # CTIs:       " << nCTI << endl;
      cout << ". # CTGs:       " << nCTG << endl;
      cout << ". # mic calls:  " << nmic << endl;
      cout << ". Queries/sec:  " << (int) (((double) nQuery) / ((double) etime) * sysconf(_SC_CLK_TCK)) << endl;
      cout << ". Mics/sec:     " << (int) (((double) nmic) / ((double) etime) * sysconf(_SC_CLK_TCK)) << endl;
      cout << ". # Red. cores: " << nCoreReduced << endl;
      cout << ". # Int. joins: " << nAbortJoin << endl;
      cout << ". # Int. mics:  " << nAbortMic << endl;
      if (numUpdates) cout << ". Avg lits/cls: " << numLits / numUpdates << endl;
    }

    friend bool check(Model &, int, bool, bool);

  };

  // IC3 does not check for 0-step and 1-step reachability, so do it
  // separately.
  bool baseCases(Model & model) {
    Minisat::Solver * base0 = model.newSolver();
    model.loadInitialCondition(*base0);
    model.loadError(*base0);
    bool rv = base0->solve(model.error());
    delete base0;
    if (rv) return false;

    Minisat::Solver * base1 = model.newSolver();
    model.loadInitialCondition(*base1);
    model.loadTransitionRelation(*base1);
    rv = base1->solve(model.primedError());
    delete base1;
    if (rv) return false;

    model.lockPrimes();

    return true;
  }

  // External function to make the magic happen.
  bool check(Model & model, int verbose, bool basic, bool random) { //basic表示不对CTG作generalize
    if (!baseCases(model))
      return false;
    IC3 ic3(model);
    ic3.verbose = verbose;
    if (basic) {
      ic3.maxDepth = 0;
      ic3.maxJoins = 0;
      ic3.maxCTGs = 0;
    }
    if (random) ic3.random = true;
    bool rv = ic3.check();
    if (!rv && verbose > 1){
    cout << "\n\n\n---------WITNESS-------------\n";
    ic3.printWitness();
    } 
    if (verbose) ic3.printStats();
    return rv;
  }

}
