<p align="center">
  <img src="assets/logo.svg" alt="Caliper" width="300">
</p>

Caliper is a Lean4 DSL for measuring *precise* running time and memory usage.

It arose from zkSecurity's need to model *concrete* complexities of algorithms,
for instance, the concrete cost of witness generation, extractors, cryptographic attacks and more.
By concrete, we mean that, we can reason about e.g. attacks taking $2^{50}$ steps,
in the presence of a concrete group of size $2^{250}$. It is intended to:

- Capture the meaning of "one computation step" on a modern, real-world CPU.
- Be easy to prove statements above in Lean.
- Easily extend to also prove *asymptotic* complexity bounds.

To do this, it is a very simple imperative language modelled after the RISC-V instruction set.
Each Caliper instruction corresponds (roughly) to a single RISC-V instruction.
The only datatype in Caliper is words of a fixed size, usually 64 bits.

We hope for Caliper to become the "yardstick" by which we can compare "real world" complexity in Lean.

## Correspondence to RISC-V

A Caliper program can easily be translated into RISC-V assembly.
The only requirements are:

- Register allocation and liveness analysis: Caliper has an infinite number of registers (each of which "cost" 1 memory), while the real CPU has a finite number of registers.
- Implementing a heap: Caliper can allocate/free arrays of words of fixed/variable size, hence a heap must be implemented.

Overall the goal of Caliper is that if a Caliper program can be proven to have computational cost $n$, 
then a real RISC-V program can be written which executes in $c \cdot n$ instructions on any reasonable RISC-V CPU
where $c$ is a small constant; roughly speaking we target $c < 10$ and have some tests with unicorn engine to sanity check this.
Similarly, if a Caliper program can be proven to have memory cost $m$, 
then a real RISC-V program can be written which uses $c \cdot m$ words of memory for a constant $c$; roughly speaking we target $c \ll 2$.

## Why Not RISC-V?

A natural question is why not just use RISC-V to reason about concrete running time directly?
The answer is that reasoning about RAM machines is complicated,
in particular, requiring reasoning about memory, including aliasing of memory locations.
Caliper sidesteps this by modelling memory as arrays of words which can only be atomically allocated/freed 
and cannot be aliased (there are no pointer types in Caliper, only indexes).
It also allows us to sidestep a bunch of complexity related to e.g. register spilling:
a real RISC-V CPU has only a finite number of registers, if you need additional variables in your program,
it requires the implementer loading/storing these variables from/to memory.

## Asymptotic Bounds

To enable asymptotic statements, the *register size* of Caliper is configurable,
for instance, it may be set to match the security parameter $\lambda$ of a scheme.
Enabling random access to a random memory of size $2^\lambda$.

## Outside The Scope

Caliper does not model all parts of a modern CPU,
and hence, Caliper performance is not 1-to-1 with runtime performance:
for instance, Caliper does not model caches, branch prediction, out-of-order execution, pipeline stalls or intrinsics available on some CPUs.
We think that modelling these, for theoretic purposes, would needlessly complicate the model and make comparison harder.

## Building

```
lake exe cache get
lake build
```
