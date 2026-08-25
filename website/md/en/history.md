# Symbolic Reasoning and Machine Proof: Project History

<br>

## 2008 — Axiomatic proving on symbolic computation

From 2008, while learning C++, the author began a long-term effort to build an **axiomatic, machine-checkable** mathematical proof environment—assisting complex reasoning and exploring gradual automation. Work proceeded mainly in spare time. The first implementation used C++, built on the German open-source library [GiNaC](https://www.ginac.de/), with semi-mechanized derivation carried out through symbolic computation.

Limited by available skills at the time, C/C++ was the primary language. Its influence persists in code style, for example:

- Overloaded output for equations: `Eq << Equal(a, b)` (analogous to `cout << "Hello World";`)
- Lambda-style notation in LaTeX: `Lamda[k] (h[k])`, resembling C++ lambdas `[k]{return h[k];}`
- Object operations via `this`, e.g. `Eq << Eq[-1].this.rhs.simplify()`

## 2016 — Open-source ecosystem and proof-as-program

Around 2016, the author surveyed open symbolic computation and proof-assistant resources, including [SymPy](https://www.sympy.org/en/index.html) and its C++ subproject [SymEngine](https://github.com/symengine/symengine), the Common Lisp system [Maxima](http://maxima.sourceforge.net), the integrated environment [SageMath](https://www.sagemath.org/) (combining Maxima, [Maple](https://www.maplesoft.com/products/Maple/), Mathematica, [MATLAB](https://www.mathworks.com/products/matlab.html), SymPy, and others), the [Theorem Prover Museum](https://theoremprover-museum.github.io/), and literature on [proof assistants](https://en.wikipedia.org/wiki/Proof_assistant) and [interactive proof systems](https://en.wikipedia.org/wiki/Interactive_proof_system).

Reading and experiments led to the [Curry–Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) (“proof as program”) as an architectural basis. Python had meanwhile become dominant in algorithms and machine learning: faster to develop than C++ (though typically slower at runtime) and closer in syntax to mathematical notation. The project was gradually **rewritten in Python**.

## 2018 — lemma.cn and an open theorem library

In 2018, the author launched [lemma.cn](../axiom) to publish the axiomatized semi-mechanized prover and growing theorem library. The aim was community collaboration to extend formal coverage; at sufficient scale, the library could support learning-based methods, while a complete formalized corpus would still require long-term collective effort.

## 2021 — Symbolic reasoning plus neural models (Inter-GPS)

In 2021, Lupantech et al. released **Inter-GPS**, a Transformer-based geometry solver combining formal statements, large-scale data, sequence models, and symbolic steps—a reference path toward general machine solving: express problems in a formal language, build training data, predict theorem-invocation sequences, and finish derivations with symbolic algorithms.

- Project page: <https://lupantech.github.io/inter-gps/>
- Code: <https://github.com/lupantech/InterGPS>
- Paper: <https://arxiv.org/pdf/2105.04165.pdf>

## 2023 — Process supervision and formal reasoning data (OpenAI)

In 2023, OpenAI released roughly **800k** examples related to process supervision for mathematical reasoning:

- <https://openai.com/research/improving-mathematical-reasoning-with-process-supervision>
- Paper: <https://arxiv.org/abs/2305.20050>

The author also outlined a formal “math GPT” pipeline: (1) a **formal logic layer** in Python (and later Lean and similar languages), with natural language for exposition only; (2) a **reward model** guided by interpreter outputs (e.g. LaTeX); (3) **reinforcement learning** over generated code. This aligns with today’s **LLM coding agents plus kernel checking**; trust still rests on formal verification, not model text alone.

## 2024 — Lean 4 core and dual-track repository

From 2024, the core library migrated to [Lean 4](https://lean-lang.org/) on dependent type theory ([math-proof/lemma](https://github.com/math-proof/lemma), `main` branch). [SymPy](https://www.sympy.org/en/index.html) interactive exploration with `apply`/`prove` remains on `master`—a dual track of **kernel-checked proofs** and **symbolic interaction**. Roughly **5000** theorems and **100k** lines of Lean source cover `Tensor` calculus, real analysis, and algorithmic properties. [lemma.cn](../index.php) offers search (`index.php?q=…`), callee/caller dependency views, and online Lean/LaTeX presentation.

## 2025 — Roadmap, agent-assisted proving, and algorithm formalization

Around 2025, the project published a [research roadmap](../endeavour): phase 2 targets **one million** theorems (with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) already at the **100k** scale in Lean); phase 3 adopts **LLM coding agents** in a human-in-the-loop loop, aligned with repository-grounded tools such as Cursor Agent and LeanDojo. On the algorithm–mathematics side, incremental **KV cache** attention for GPT-style decoding was formalized in both SymPy and Lean 4 (see [KV cache note](../arxiv/kv_cache/main.md); arXiv PDF pending), illustrating a path from production algorithm semantics to machine-checkable lemmas.
