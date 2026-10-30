# What is lemma.cn
  <br>

[lemma.cn](../index.php) is a formalized theorem library for algorithms, first developed in [Python](../../py/website/index.php). It primarily relies on the open-source symbolic computation project [SymPy](https://github.com/sympy/sympy) for interactive exploration and adaptation. Its function naming conventions are largely inspired by the mathematical software language [Mathematica](https://reference.wolfram.com/language/index.html.en?source=footer). Later, to pursue greater logical rigor and completeness, it was rewritten using the [Lean](https://github.com/math-proof/lemma/tree/main) proof assistant, which is based on Dependent Type Theory (DTT).
Its main features are: interactivity (ITP), axiomatization, and code as proof.
The fundamental design philosophy is: precise syntax, concise expression, efficient execution, and aesthetically pleasing notation, striving to embody the aesthetic standards of mathematics: theoretical perfection, structural symmetry, and universal applicability.


* By *interactive*, it means that fully automated theorem proving (ATP) is not currently achievable. Human assistance is required: people search the theorem library and tell the computer which theorems to apply to which kinds of problems.
* By *axiomatization*, it means following [Hilbert's program](https://en.wikipedia.org/wiki/Hilbert%27s_program): every proved mathematical theorem is derived in finitely many steps from axiom schemas and inference rules, strictly formalized in the framework of dependent type theory.
* By *code as proof*, via the Curry–Howard correspondence, mathematical propositions are described exactly by [Lean](https://lean-lang.org/) statements; the proof is a well-typed program, without substituting checkable steps with natural-language shortcuts such as “evidently,” “it is easy to see,” “similarly,” “in general,” “and so on,” “conversely,” “in summary,” or “without loss of generality.” Under Lean 4’s exact real and hyperreal semantics, there is no floating-point rounding error as in ordinary numerical code.


# Building the Algorithm Theorem Repertoire
  <br>
  
The library currently contains <label id=count>5000</label> proved theorems (<label id=lines>100000</label> lines of Lean) for interactive derivation, covering:

* [Bool](../?module=Bool) Elementary logical (Boolean) operations
* [Fin](../?module=Fin) Elementary algebra of finite sets of natural numbers
* [Nat](../?module=Nat) Elementary algebra of natural numbers
* [Int](../?module=Int) Elementary algebra of integers
* [Rat](../?module=Rat) Elementary algebra of rationals
* [Real](../?module=Real) Algebra and real analysis, e.g.:
  - [Jensen's inequality](../?module=Real.LeSum_Mul.of.EqSumRange__1.All_Ge_0.All_In_Icc.All_Gt0Deriv2.ContinuousOn_Icc.main)
* [Hyperreal](../?module=Real) Nonstandard analysis
* [Complex](../?module=Complex) Complex analysis, e.g.:
  - [quartic equation](../?module=Complex.Eq0Add_Mul_Pow_4.is.In_Ite_FinsetSSubS__SubS.of.Ne_0)
  - [closed form of homogeneous linear recurrence with constant coefficients](../?module=Complex.Any_All_Eq_Dot_MulDescFactorial.of.All_Eq_Dot)
* [Set](../?module=Set) Set theory
* [Finset](../?module=Finset) Finite set theory, e.g.:
  - [k-means clustering](../?module=Finset.LeAddSumS_SquareSub_Div_Sum.of.LeAbsSSub_Div_Sum.NotIn.In.GtCard_0)
* [List](../?module=List) Finite list theorems
* [Vector](../?module=Vector) One-dimensional vector theorems
* [Matrix](../?module=Matrix) Matrix theory, e.g.:
  - [Okishio's theorem](../?module=Matrix.Any_And_EqSMul_UpdateCol.of.IsIrreducibleUpdateColAdd_Dot.LtDot_Add_SMul.EqSMul.All_Gt_0)
  - [Cholesky decomposition](../?module=Finset.And.of.Eq_Adjoint.Imp_Gt_0.Eq_Ite.Cholesky)
  - [PLU decomposition](../?module=Tensor.Eq.Dot.PLU.of.Eq.Eq_Dot.Eq_Ite)
* [Tensor](../?module=Tensor) Formal tensor calculus, semantically equivalent to **torch.Tensor**, for formal verification of deep-learning algorithms, e.g.:
  - [kv_cache](../?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T)
  - [RoPE](../?module=Tensor.DotSoftmaxDivDot_Stack_TDot.eq.Stack_Div_SumExp.of.Eq_Stack_Mul)
* [Random](../?module=Random) Probability theory and stochastic processes, e.g.:
  - [𝒳²(n)](../?module=Random.Distributed.ChiSquared.of.All_Distributed_Gaussian.All_Indep), [sum of independent Gaussians](../?module=Random.DistributedSum.of.All_Distributed_Gaussian.All_Indep)
  - [naive Bayes document classification](../?module=Random.ArgMax_ProbCond.eq.ArgMax_Mul_Prod_ProbCond.of.NeProbJoint__0.All_CondIndep)
  - [CRF loss function](../?module=Random.All_Eq_AddLogSumExpAdd.All_EqNegLogProb.of.All_Eq_LogProbCond.All_Eq_LogProbCond.Eq_LogProbJoint.All_Lt0ProbJoint.IsDiscreteHMM), [Viterbi](../?module=Random.All_Eq_Add_MaxAdd.EqMax_ProbJoint.of.All_Eq_LogProbCond.All_Eq_LogProbCond.Eq_LogProbJoint.All_Lt0ProbJoint.IsDiscreteHMM)
  - [GAE (discrete)](../?module=Random.GradExpectDotPow_Id.eq.ExpectDot_FunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_NeProb_0.IsPolicyTrajectory.In_Icc.In_Ico), [GAE (continuous)](../?module=Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Icc.In_Ico)

<br><br>
-------
This formal algorithm theorem library supports work in algorithms and mathematical formalization—a **dynamo for thinking**: state algorithmic properties as machine-checkable propositions and prove them step by step; organize and retrieve lemmas to shorten repeated manual argument; maintain proof scripts in the online editor, with comments, Lean 4 source, and LaTeX rendered side by side as structured documents.

It serves students and researchers in mathematics and related fields, algorithm designers and analysts, and readers who consult formal proofs in teaching or self-study. The library is an interactive, searchable electronic algorithm reference written in Lean 4.
<br><br>

![](png/national_emblem.png)
[<font size=2>浙公网安备33060202000937号</font>](http://www.beian.gov.cn/portal/registerSystemInfo?recordcode=33060202000937)
[<font size=2>浙ICP备20017509号-3</font>](https://beian.miit.gov.cn/)

<script type=module>
	document.querySelector('#count').innerHTML = await get("../php/request/count.php");
  document.querySelector('#lines').innerHTML = await get("../php/request/lines.php");
</script>