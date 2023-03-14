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

#include <iostream>
#include <string>
#include <time.h>

extern "C" {
#include "aiger.h"
}
#include "IC3.h"
#include "Model.h"
int main(int argc, char ** argv) {       //命令行输入字符串数组argv，字符串个数/数组长度为argc, argv[0] = "./IC3"
  freopen("test.txt", "w", stdout);
  unsigned int propertyIndex = 0;
  bool basic = false, random = false;
  int verbose = 0;                       //默认verbose取0, 不输出日志
  cout << "argc = " << argc << endl;
  for (int i = 1; i < argc; ++i) {       //查看命令行输入的第一行信息    
    if (string(argv[i]) == "-v")         //参数-v   日志输出变量verbose取2
      // option: verbosity
      verbose = 2;
    else if (string(argv[i]) == "-s")    //参数-s
      // option: print statistics
      verbose = max(1, verbose);
    else if (string(argv[i]) == "-r") {  //参数-r
      // option: randomize the run, which is useful in performance
      // testing; default behavior is deterministic
      srand(time(NULL));
      random = true;
    }
    else if (string(argv[i]) == "-b")    //参数-b
      // option: use basic generalization
      basic = true;
    else
      // optional argument: set property index
      propertyIndex = (unsigned) atoi(argv[i]);
  }
  cout << "verbose = " << verbose << endl;
  // read AIGER model 输入aiger格式源文件
  aiger * aig = aiger_init();
  
  const char * msg = aiger_read_from_file(aig, stdin);
  if (msg) {
    cout << msg << endl;
    return 0;
  }
  cout << "read aig successfully" << endl;
  // create the Model from the obtained aig 通过aiger建立模型
  Model * model = modelFromAiger(aig, propertyIndex);
  aiger_reset(aig);
  if (!model) return 0;
  cout << "model created successfully" << endl;

  	
  // model check it
  bool rv = IC3::check(*model, verbose, basic, random);
  // print 0/1 according to AIGER standard
  cout << !rv << endl;

  delete model;
  
  return 1;
}
