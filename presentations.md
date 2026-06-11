# CSE 290Q Final Presentations

[Link to schedule](https://github.com/kmill/cse290q-26sp/blob/main/presentations.md)

## Session 1: Thursday, June 11

Location: Baskin 165

### 12:00–12:15. Formally Verifying Distributed Systems Protocols in Veil

**Sabrina Reis**

*Abstract.* Distributed systems are the backbone of many industries. Formal verification is a key part of ensuring these systems function as expected by specifying system behavior and ensuring that system implementations adhere to these specifications. In this project, I explore using a Lean library called Veil to verify distributed systems protocols. In particular, I investigate the viability of integrating Veil into the Ironwright project, which draws on manual and automatic verification methods to offer a promising hybrid approach to systems verification. My talk will cover the process of learning Veil as a Lean non-expert, an implementation and evaluation of a prototypical distributed systems protocol, and the potential role of Veil in Ironwright.

### 12:15–12:30. Teaspoon: Liquid Types and More for TypeScript

**Nicola Gannon**

*Abstract.* Static type systems for programming languages provide stronger guarantees of program correctness. Through analysis at compile time, static type systems typically eliminate all runtime type errors and enforce proper usage of APIs. The programmer can even lean on the type system to help her reason about the nature of her data. The benefits of static typing are best showcased in web development. Webpages are programmed in JavaScript, a dynamically typed programming language. But most[^1] web developers use TypeScript, a statically typed extension to JavaScript. TypeScript is a compiler-as-specification, which works remarkably well in practice, but a robust theory would prevent soundness bugs. Teaspoon aims to do what TypeScript did for JavaScript. It extends a subset of TypeScript, formally backing it with the usual operational semantics, type inference, and constraint solving. Teaspoon's type system is unusual in its support for mutability and imperative programming. The addition of first-class propositions and liquid types effectively create a dependently typed TypeScript.

[^1]: https://2025.stateofjs.com/en-US/usage/#js_ts_balance

### 12:30–12:45. Relational Databases in Lean: From Queries to Proofs

**Jaisuraj Kaleeswaran**

*Abstract.* Relational databases power modern software at massive scale, but the correctness of the fundamental operations of selection, projection and join has very rarely been formally proven. Lean 4 is able to define relational operations as functions on typed records such that the same code serves as both a query engine and a formal proof. I will present definitions of database constructs in Lean and build a macro that enables queries to be specified like LINQ and to prove correctness of relational operations.

### 12:45–13:00. Toward Verifiable Reasoning in LLMs

**Zekun Zhao**

*Abstract.* Chain-of-thought (CoT) prompting can improve final-answer performance, but it does not guarantee that intermediate reasoning steps are faithful, valid, or checkable. This work studies how formal methods can make natural-language reasoning more reliable by translating CoT rationales into Lean artifacts, checking the resulting theorem statements and proofs, and using compiler feedback to diagnose and repair failures.

### 13:00–13:15. A Benchmark for Frontier LLMs on Program-Verification Proof Obligations in Lean

**Soham Rajadhyaksha**

*Abstract.* LLMs are increasingly used to help write verified software, but it is unclear how to evaluate them on the routine proof obligations that arise in practice. I will present a Lean benchmark of such obligations and show how benchmark construction and harness design can substantially influence measured model performance.

### 13:15–13:30. Intrinsically Typed Verified Compiler with Reusable Proof Automation

**Sean Gray**

*Abstract.* Verified compilation establishes by machine-checked proof that a compiler preserves the meaning of source programs, but such proofs are large and dominated by repetitive, per-construct reasoning. We describe a verified compiler in Lean 4 from an intrinsically typed expression language to a type-indexed stack machine, whose typed output is erased to a flat, untyped instruction set executed by a small interpreter, with the executed result proved to agree with a big-step operational semantics of the source. The presentation centers on a reusable proof tactic whose rewrite set spans both the typed and the untyped stack machines, so that the denotational and operational correctness theorems are discharged uniformly.

### 13:30–13:45. *Coffee break*

### 13:45–14:00. Homomorphic Encryption: Proving noise bounds for ring operations

**Cheuk Pui Lam**

*Abstract.* BFV is one of the most popular homomorphic encryption schemes, and in every homomorphic operation `(+, *)`, there is noise introduced. We follow the paper by Fan and Vercauteren to show a construction for the somewhat homomorphic encryption scheme, from the ground up including some proofs for the algebraic structure, and show correctness in the error bounds for these HE operations.	

### 14:00–14:15. Reasoning About Mastermind

**Jeromey Klein**

*Abstract.* The game of mastermind can be difficult for players to understand. If the player who is the oracle makes a mistake, the game is ruined and cannot be played. I present a formalization of the game and a method for proving whether a game state is correct or incorrect. I also present proofs on the correctness of my formalization.

### 14:15–14:30. Text-to-Video RAG Pipeline with Dependent Types in Lean

**Serene Cheng**

*Abstract.* AI generation systems typically have pipelines with LLM calls, retrieval systems, scoring functions, and other models. They have good results, but their correctness prompts are often only enforced with prompts and comments at runtime. My project investigates how dependent types can be used to formally model and verify workflows. I use Lean to develop a formal representation of a text-to-video retrieval-augmented generation (RAG) pipeline inspired by a Python system that performs web retrieval, image retrieval, script generation, critique and revision, video generation, and post-processing. Important pipeline invariants, like shot structure, narration length, bounded critique scores, workflow ordering, video-narration synchronization, and critique loop termination are encoded in the type system. Invalid states are unrepresentable, so errors can be detected at compile time. I demonstrate that dependent type theory can be a foundation for building reliable AI pipelines.

### 14:30–14:45. Mlkih: An NbE-Based Experimental Lean 4 Kernel Checker

**Yipeng Liu**

*Abstract.* This project implements an experimental Lean 4 export checker in Haskell using normalization by evaluation. The checker represents elaborated expressions as semantic values with closures, neutral spines, delayed definitions, and thunks, and implement many Lean 4 kernel mechanisms including iota reduction, projection reduction, structure eta, proof irrelevance, universe-level comparison, and selected primitive reductions. It passes the Kernel Arena tutorial export cases and several unit tests, but the thunk evaluator dose not check all Lean's `Init`; symbolic `Nat` proofs such as `Nat.bitwise_lt_two_pow` led to repeated recursive reductions and insufficient sharing. A work-in-progress abstract machine branch succeeded on this benchmark, indicating the conclusion that NbE is a feasible method and the next step is to give a stronger call-by-need operational structure.

### 14:45–15:00. Formalizing a Memory Prefetcher Model in Lean

**Michelle Gurovith**

*Abstract.* Memory prefetching is a systems optimization where future memory accesses are predicted and loaded early to reduce cache misses. I formalized a small tutorial-style model of prefetching in Lean 4, including finite traces, infinite streams, a simple cache model, online prefetchers, and oracle prefetchers. I will discuss the modeling choices, show executable examples, and explain how the formalization clarifies the benchmark relationship between real online prefetchers and an oracle with future knowledge.

## Session 2: Asynchronous

These talks will be prerecorded and posted to Zulip for asynchronous Q/A.

### A lightweight reinforcement learning theorem prover for Lean 4

**Creighton Glasscock**

*Abstract.* Before LLMs became popular theorem provers, a line of work in automated theorem proving trained small reinforcement-learning policies to select proof tactics and paired them with explicit search. Deep reinforcement learning requires no pre-written proofs and can produce models many orders of magnitude smaller than current LLM provers. I train prover models with PPO for tactic and local premise selection, then, in line with existing works in other ITPs, pair the trained policy with a best-first search at proof time. I evaluate these models in Lean4 in the domains of propositional natural deduction and Peano arithmetic. I also experiment with behavior cloning (BC) for warm-start training and with curriculum learning with increasing difficulty during training in order to address the sparse reward problem. In my presentation, I will walk through this approach and compare my results in an ablation experiment,  then give a live demo of my trained prover models invoked as Lean4 closer tactics.

### Proof Techniques in Lean 4 — A Learner's Case Study on Sorting Algorithms and Recursive Data Structures

**Aditya Sarin**

*Abstract.* Lean 4's Mathlib already contains verified sorting algorithms, but the proof techniques behind them are rarely explained for newcomer CS students like freshman-sophomore year students. My project systematically compares functional induction and structural induction on merge sort and insertion sort, and it also documents what each approach feels like from a learner's perspective. The result is a pedagogical artifact, annotated Lean 4 proofs with exercise files for CS students new to formalization.

### How Frontier LLMs Fail at Lean

**Mukund Ojha**

*Abstract.* The Lean theorem proving leaderboard is dominated by specialist fine tuned provers such as Goedel-Prover-V2, DeepSeek-Prover-V2, StepFun-Prover, Leanabell most reporting pass@k on the original miniF2F. 

Two questions remain underexplored:
- First, frontier general purpose models (Claude,GPT, Gemini), which a practitioner with API access can reach, are benchmarked on Lean less systematically than specialist provers existing evaluations such as IndiMathBench and the Open Proof Corpus use miniF2F-v1 or different benchmarks entirely. 
- Second, the field reports pass rates but rarely characterizes how proofs fail or how much measured performance is attributable to memorization rather than reasoning.
