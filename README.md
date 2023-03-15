## To do

change memory.sv with different paramaters



## To Use

The *tests* folder stores memory.sv with different parameters, along with the aiger format of memory.sv. The name of memory.sv indicates its specific parameters. For example, *memory_8_4.sv* means the top module has WIDTH = 8, PSIZE = 4.

1. At memory_MC/yosys, use ./yosys to run yosys.

2. In Yosys Open SYnthesis Suite, use command:
   ```
    read_verilog -formal  ../tests/memory_32_4.sv
    prep -top TOP
    flatten
    memory -nordff
    setundef -undriven -init -expose
    delete -output
    techmap
    abc -fast -g AND
    write_aiger -zinit -ascii ../tests/memory_32_4.aag

   ```
3. At memory_MC/ic3ref, make.

4. At memory_MC/ic3ref, use command:
    ```
    ./IC3 -v -b < ../tests/memory_32_4.aag
    ```



## Result

|  WIDTH/PSIZE   |   8/4   |  16/4   |  32/4   |
| :------------: | :-----: | :-----: | :-----: |
| time(s)        | 0       |  1.01   |   4.2   |
|      k         | 4       |    3    |    3    |
|   Qurties      | 372     |   5822  |  11716  |
|    Ctis        | 32      |   563   |   1131  |
|    ctgs        |  0      |    0    |    0    |
|  mic calls     | 51      |   870   |   1753  |
| queries/sec    | 37200   |   5822  |  2809   |
|  mics/sec      | 5100    |    869  |   420   |
| Avg lits/cls   | 3.21569 | 4.09028 | 4.10086 |
