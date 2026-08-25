# Research roadmap

[lemma.cn](../../index.php) aims long-term at **mathematics mechanization**, in a direction related to the [Key Laboratory of Mathematics Mechanization, CAS](http://www.mmrc.iss.ac.cn/). Fully automated mathematical proof remains an open problem for publicly accessible formal resources. This project seeks to build an **axiomatic, machine-checkable, open-source** theorem library and proof environment in stages.

The library currently contains roughly 5000 theorems checked in Lean 4 (see the count on the home page), spanning several mathematical domains. Planned phases:

1. **Rule-based interactive proving (largely in place)**  
   A semi-mechanized environment based on dependent type theory and a lemma library is operational; ongoing work covers bug fixes, lemma extension, and tooling.

2. **Large-scale theorem repository (in progress)**  
   Target: **one million** reusable formal theorems in this project’s unified framework (`Tensor` calculus and related domains). [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) in the Lean ecosystem has already reached the **100,000** scale, showing that such growth is feasible in dependent type theory; this project aims at formal coverage on the rough historical scale of all proved mathematical theorems humanity has accumulated (about **one million**). Long-term, community effort; timeline depends on contribution volume.

3. **LLM coding agents for proof assistance (in progress)**  
   On top of the phase-2 library and Lean sources, adopt the current **coding-agent** paradigm: large language models operate in a **human-in-the-loop** loop—reading repository context, invoking tools (lemma search, `lake build`, LSP diagnostics, callee/caller dependency graphs, etc.), and drafting or completing proof scripts; humans review and revise, while the **Lean 4 kernel** remains the authority. This mirrors state-of-the-art agent workflows in software engineering—**repository grounding** (RAG / whole-repo indexing), **tool use** (terminal, build, language server), and **edit–compile–fix** iteration (as in [Cursor Agent](https://cursor.com/), GitHub Copilot, Claude Code, and similar systems). Agents accelerate lemma retrieval, tactic choice, and proof drafting; they do **not** replace formal checking. Related work in formal proving includes [LeanDojo](https://leandojo.org/) (retrieval-augmented theorem proving in Lean), [ProofNet](https://proofnet.github.io/) (undergraduate-math Lean autoformalization benchmark), and [GPT-f](https://arxiv.org/abs/2109.04561) (early LLM-assisted formal proof); this project emphasizes integrating coding agents with the **lemma.cn** library and web search interface rather than end-to-end automated proving competitions.

4. **Semi-supervised / unsupervised theorem discovery (research)**  
   Explore proposing candidate statements from the existing library and attempting proofs from known lemmas, strictly separating conjectures from checked theorems.

5. **Unified abstract mathematics and programming languages (long-term)**  
   Build on the above so computer systems can more systematically state, compose, and verify abstract mathematical structure as infrastructure for research and algorithmic formal verification.

This roadmap describes research directions and milestones, not a committed schedule or guaranteed technical path. Each phase can be pursued while using the theorem library and Lean 4 artifacts already published.
