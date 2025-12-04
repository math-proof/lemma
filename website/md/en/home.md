# What is lemma.cn
  <br>
  
[lemma.cn](../index.php) is a formalized theorem library for algorithms, initially developed in [Python](../../py/website/index.php). It primarily relies on the open-source symbolic computation project [SymPy](https://github.com/sympy/sympy) for interactive exploration and adaptation. Its function naming conventions are largely inspired by the mathematical software language [Mathematica](https://reference.wolfram.com/language/index.html.en?source=footer). Later, to pursue greater logical rigor and completeness, it was entirely rewritten using the [Lean](https://github.com/math-proof/lemma/tree/main) proof assistant, which is based on Dependent Type Theory (DTT).  

Its main features include: interactivity (ITP), axiomatization, and the principle of "code as proof."  

The fundamental design philosophy is: precise syntax, concise expression, efficient execution, and aesthetically pleasing notation, striving to reflect the aesthetic standards of mathematics: theoretical perfection, structural symmetry, and universal applicability.  

* By "interactive," it means that fully automated theorem proving (ATP) is not currently achievable. Instead, human brain assistance is required, where humans search the theorem library and instruct the computer on which theorems to apply for specific types of problems.  
* By "axiomatization," it refers to adhering to the principles of [Hilbert's program](https://en.wikipedia.org/wiki/Hilbert%27s_program), where all proven mathematical theorems are derived within a finite number of steps from axiom schemas and inference rules, strictly formalized within the framework of Dependent Type Theory.  
* By "code as proof," it means that, based on the **Curry-Howard correspondence**, mathematical propositions are precisely described using [Lean](https://lean-lang.org/) statements. The code itself constitutes the proof process, eliminating the ambiguity inherent in natural language—terms such as "evidently/obviously/conspicuously," "similarly/likewise" "easily seen," "generally/equivalently" "conversely/and so on," "conversely," "in summary/put it in a nutshell" or "without loss of generality" are absent. In Lean 4 formalized proofs, there are no rounding errors caused by floating-point numbers as in other programming languages.   

One can easily locate the website information in the Google search engine: [定理库](https://www.google.com.hk/search?q=%E5%AE%9A%E7%90%86%E5%BA%93).  
In the open-source community, automatic thoerem libraries include: [leanprover](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Algebra/Basic.html), [coq](https://github.com/coq/coq) and [isabelle](https://isabelle.in.tum.de/).

<br><br>
------
To master the theorem derivation system proficiently, it is essential to grasp several common reasoning methods:

## Formal Reasoning Strategies
1. **Induction**  
Induction refers to mathematical induction, which essentially involves reasoning from the specific to the general: `induction`.

2. **Deduction**  
Deduction is the inverse process of induction, essentially reasoning from the general to the specific (elimination of universal quantifiers): `specialize`/`intro`/`rintro`.

3. **Proof by Contradiction**  
Proof by contradiction, also known as reductio ad absurdum, assumes the proposition is false and attempts to derive a contradiction based on the [Law of Excluded Middle](../?module=Bool.Or_Not): `by_contra`.

4. **Case Analysis**  
Case analysis involves breaking down a complex problem into several simpler subproblems for reasoning: `by_cases`/`interval_cases`/`rcases`.

5. **Abductive Reasoning**  
Abductive reasoning is a method of inferring possible causes from known results. It starts from the proposition to be proven and derives the sufficient conditions required for the proposition to hold: `refine`/`apply`.

## Heuristic-Assisted Reasoning
**Analogy** is a reasoning method from known specifics to unknown specifics. For example, attempting to transfer a proposition from the real number domain to the hyperreal number domain to check if it still holds.


# The construction of Mathematical Theorem Repertoire
  <br>
  
As of this writing, the system has accumulated <label id=count>5000</label> proven theorems (with <label id=lines>100000</label> lines of lean code) for interactive derivation, covering:

* [Bool](../?module=Bool) Elementary logical (boolean) operations
* [Fin](../?module=Fin) Elementary algebra of finite sets of natural numbers
* [Nat](../?module=Nat) – Elementary algebra related to natural numbers  
* [Int](../?module=Int) – Elementary algebra related to integers  
* [Rat](../?module=Rat) – Elementary algebra related to rational numbers  
* [Real](../?module=Real) – Algebra and real analysis related to real numbers  
* [Hyperreal](../?module=Real) – Non-standard analysis  
* [Complex](../?module=Complex) – Algebra and complex analysis related to complex numbers  
* [Set](../?module=Set) – Set theory  
* [Finset](../?module=Set) – Finite set theory  
* [List](../?module=List) – Finite list theorem library  
* [Vector](../?module=Vector) – One-dimensional vector theorem library  
* [Tensor](../?module=Tensor) – Formal tensor calculus theorem library, where the concepts and operators are semantically equivalent to **torch.Tensor**, used for formal verification of deep learning algorithms

<br><br>
-------
This formal algorithm theorem library enables algorithm researchers to conveniently analyze algorithmic principles, simplify verification processes, and essentially "put an engine into thinking." It is primarily applicable for theoretical mathematical proofs, offering reference value for mathematics students and researchers, as well as algorithm engineers and researchers during algorithmic studies and mathematical analysis.  

It also supports mathematical professionals in organizing mathematical theorem knowledge. Through the online code editor, users can edit theorem procedures to systematize mathematical theorems, with quick and convenient functions for locating definitions of theorems, functions, and symbols. By seamlessly integrating natural language annotations, Lean4 code, and LaTeX formulas, it enables multimodal structured document presentation and automatically generates frontend-visualized LaTeX formulas, effectively replacing traditional pen-and-paper calculations.  

With its practical value of simplifying complexity for both research and teaching, it serves as an electronic algorithm reference book written in the Lean4 language.
<br><br>

<script type=module>
	$('#count').innerHTML = await get("../php/request/count.php");
  $('#lines').innerHTML = await get("../php/request/lines.php");
</script>