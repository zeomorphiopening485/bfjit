# Brainf_ck JIT Compiler

This is a JIT compiler for the Brainf\_ck programming language, implemented in C using LLVM. It takes a Brainf\_ck program as input and compiles it to machine code at runtime, allowing for fast execution of Brainf\_ck programs.

## Benchmarks

The benchmark results comparing it to unoptimized Brainf\_ck implementations written in JavaScript and C are as follows:

<!-- benchmark:start -->
```text
Benchmark 1: ./build/bfjit ./examples/hanoi.b.txt
  Time (mean ± σ):     426.8 ms ±   6.9 ms    [User: 404.8 ms, System: 21.8 ms]
  Range (min … max):   420.5 ms … 440.0 ms    10 runs
 
Benchmark 2: ./build/simple_c ./examples/hanoi.b.txt
  Time (mean ± σ):     12.448 s ±  0.762 s    [User: 12.445 s, System: 0.001 s]
  Range (min … max):   11.591 s … 13.378 s    10 runs
 
Benchmark 3: bun ./benchmark/bf.js ./examples/hanoi.b.txt
  Time (mean ± σ):     25.604 s ±  0.417 s    [User: 25.614 s, System: 0.028 s]
  Range (min … max):   24.427 s … 25.851 s    10 runs
 
Summary
  ./build/bfjit ./examples/hanoi.b.txt ran
   29.16 ± 1.85 times faster than ./build/simple_c ./examples/hanoi.b.txt
   59.99 ± 1.38 times faster than bun ./benchmark/bf.js ./examples/hanoi.b.txt
```
<!-- benchmark:end -->

## License

This project is licensed under the MIT License.
