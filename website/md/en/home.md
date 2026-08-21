# What is lemma.cn
  <br>

[lemma.cn](../index.php) is a formalized theorem library for algorithms, first developed in [Python](../../py/website/index.php). It primarily relies on the open-source symbolic computation project [SymPy](https://github.com/sympy/sympy) for interactive exploration and adaptation. Its function naming conventions are largely inspired by the mathematical software language [Mathematica](https://reference.wolfram.com/language/index.html.en?source=footer). Later, to pursue greater logical rigor and completeness, it was rewritten using the [Lean](https://github.com/math-proof/lemma/tree/main) proof assistant, which is based on Dependent Type Theory (DTT).
Its main features are: interactivity (ITP), axiomatization, and code as proof.
The fundamental design philosophy is: precise syntax, concise expression, efficient execution, and aesthetically pleasing notation, striving to embody the aesthetic standards of mathematics: theoretical perfection, structural symmetry, and universal applicability.


* By *interactive*, it means that fully automated theorem proving (ATP) is not currently achievable. Human assistance is required: people search the theorem library and tell the computer which theorems to apply to which kinds of problems.
* By *axiomatization*, it means following [Hilbert's program](https://en.wikipedia.org/wiki/Hilbert%27s_program): every proved mathematical theorem is derived in finitely many steps from axiom schemas and inference rules, strictly formalized in the framework of dependent type theory.
* By *code as proof*, it means that, via the Curry–Howard correspondence, mathematical propositions are described exactly by [Lean](https://lean-lang.org/) statements. The code itself is the proof; there is no ambiguity of natural-language phrases such as “evidently,” “similarly,” “it is easy to see,” “in general,” “and so on,” “conversely,” “in summary,” or “without loss of generality.” Lean 4 formal proofs also have none of the rounding error caused by floating-point numbers in other programming languages.

The site can be found via Google: [定理库](https://www.google.com.hk/search?q=%E5%AE%9A%E7%90%86%E5%BA%93).
Proof assistants / theorem libraries in the open-source community include [leanprover](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Algebra/Basic.html), [coq](https://github.com/coq/coq), and [isabelle](https://isabelle.in.tum.de/).


To use the theorem derivation system fluently, one needs several common methods of reasoning:
## Formal Reasoning Strategies
1. Induction
Induction means mathematical induction: reasoning from the particular to the general: `induction`
2. Deduction
Deduction is the inverse of induction: reasoning from the general to the particular (elimination of a universal quantifier): `specialize`/`intro`/`rintro`
3. Proof by Contradiction
Proof by contradiction, or reductio ad absurdum, assumes the proposition is false and, using the [law of excluded middle](../?module=Bool.Or_Not), tries to derive a falsehood: `by_contra`
4. Divide and Conquer
Divide and conquer is case analysis: splitting a hard problem into several simpler ones: `by_cases`/`interval_cases`/`rcases`
5. Abduction
Abduction infers possible causes from a known result. Starting from the goal, one derives sufficient conditions under which the goal holds: `refine`/`apply`

## Heuristic-Assisted Reasoning
- Analogy
  Analogy reasons from a known particular to an unknown particular. For example, try transferring a proposition from the reals to the hyperreals and see whether it still holds.
<br><br>
------


# Building the Algorithm Theorem Repertoire
  <br>
  
The library currently contains <label id=count>5000</label> proved theorems (<label id=lines>100000</label> lines of Lean) for interactive derivation, covering:

* [Bool](../?module=Bool) Elementary logical (Boolean) operations
* [Fin](../?module=Fin) Elementary algebra of finite sets of natural numbers
* [Nat](../?module=Nat) Elementary algebra of natural numbers
* [Int](../?module=Int) Elementary algebra of integers
* [Rat](../?module=Rat) Elementary algebra of rationals
* [Real](../?module=Real) Algebra and real analysis
* [Hyperreal](../?module=Real) Nonstandard analysis
* [Complex](../?module=Complex) Complex analysis, e.g.:
  - [quartic equation](../?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0)
* [Set](../?module=Set) Set theory
* [Finset](../?module=Set) Finite set theory
* [List](../?module=List) Finite list theorems
* [Vector](../?module=Vector) One-dimensional vector theorems
* [Tensor](../?module=Tensor) Formal tensor calculus, semantically equivalent to **torch.Tensor**, for formal verification of deep-learning algorithms, e.g.:
  - [kv_cache](../?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T)

<br><br>
-------
This formal algorithm theorem library helps algorithm researchers analyze principles, shorten arguments, and “put an engine on thinking.” It is mainly useful for theoretical mathematical proof, and can serve as a reference for mathematics students and researchers, as well as algorithm engineers and researchers in algorithm work and mathematical analysis.
It also helps mathematicians organize theorem knowledge: with the online code editor one can edit proofs, collect theorems, and quickly locate definitions of theorems, functions, and symbols. Natural-language comments, Lean 4 code, and LaTeX formulas are interleaved and translated among each other, yielding a multimodal structured document and automatically rendered LaTeX, a substitute for pen-and-paper calculation.
It simplifies both research and teaching, and is an electronic algorithm reference written in Lean 4.
<br><br>

![](png/national_emblem.png)
[<font size=2>浙公网安备33060202000937号</font>](http://www.beian.gov.cn/portal/registerSystemInfo?recordcode=33060202000937)
[<font size=2>浙ICP备20017509号-3</font>](https://beian.miit.gov.cn/)

<script type=module>
	$('#count').innerHTML = await get("../php/request/count.php");
  $('#lines').innerHTML = await get("../php/request/lines.php");
</script>