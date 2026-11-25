# Algorithm Theorem Repertoire

A statement is a [Lean](https://lean-lang.org/) proposition, and its proof is a program that typechecks. That is *code as proof*, in the sense of the Curry–Howard correspondence: a gap is not filled by ““similarly/in general/in summary/and so on/evidently/conversely/it is easy to see/without loss of generality.” Real and hyperreal numbers are exact, so these proofs do not inherit the rounding of ordinary floating-point code.

The library currently contains <label id=count>5000</label> proved theorems (<label id=lines>100000</label> lines of Lean) for interactive derivation, covering:

* [Bool](../?module=Bool) Elementary logical (Boolean) operations
* [Fin](../?module=Fin) Elementary algebra of finite sets of natural numbers
* [Nat](../?module=Nat) Elementary algebra of natural numbers
* [Int](../?module=Int) Elementary algebra of integers
* [Rat](../?module=Rat) Elementary algebra of rationals
* [Real](../?module=Real) Algebra and real analysis, e.g.:
  - [Jensen's inequality](../?module=Real.LeSum_Mul.of.EqSumRange__1.All_Ge_0.All_In_Icc.All_Gt0Deriv2.ContinuousOn_Icc)
* [Hyperreal](../?module=Hyperreal) Nonstandard analysis
* [Complex](../?module=Complex) Complex analysis, e.g.:
  - [quartic equation](../?module=Complex.Eq0Add_Mul_Pow_4.is.In_Ite_FinsetSSubS__SubS.of.Ne_0)
  - [closed form of homogeneous linear recurrence with constant coefficients](../?module=Complex.Any_All_Eq_Dot_MulDescFactorial.of.All_Eq_Dot)
  - [Mersenne's law](../?module=Complex.Eq_Mul_SqrtDiv.of.All_EqDeriv_Mul_ExpMulIArctanDeriv.All_Eq_MulMul_Sin_Cos)
  - [catenary](../?module=Complex.Any_Eq_AddMul_CoshDivSub.of.All_EqDeriv_Mul_ExpMulIArctanDeriv.ContDiff_2.Differentiable)
* [Set](../?module=Set) Set theory
* [Finset](../?module=Finset) Finite set theory, e.g.:
  - [k-means clustering](../?module=Finset.LtAddSumS_SquareSub_DivSum.of.LtAbsSSub_DivSum.NotIn.In.GtCard_0)
* [List](../?module=List) Finite list theorems
* [Vector](../?module=Vector) One-dimensional vector theorems
* [Matrix](../?module=Matrix) Matrix theory, e.g.:
  - [Okishio's theorem](../?module=Matrix.Any_And_EqSMul_VecMul_UpdateCol.of.IsIrreducibleUpdateColAdd_Dot.LtDot_Add_SMul.EqSMul.All_Gt_0)
  - [Cholesky decomposition](../?module=Matrix.Eq_Mul_Adjoint.of.All_Eq_Ite__Ite_Sqrt_0.All_Lt0Dot_MulVec.EqAdjoint), [PLU decomposition](../?module=Matrix.EqMul_T_1.IsLowerTriangular.IsUpperTriangular.EqMulS)
  - [kv_cache](../?module=Matrix.XEq_Append_MulSoftmaxDivMul_AppendTSGetSlice.of.All_XEq_MulSoftmaxAddDivMul_T)
* [Tensor](../?module=Tensor) Formal tensor calculus, semantically equivalent to **torch.Tensor**, for formal verification of deep-learning algorithms, e.g.:
  - [Rotary Position Embedding](../?module=Matrix.MulSoftmaxDivMulStack_MulGetS__T_SqrtAdd.eq.Stack_DivSumS)
* [Random](../?module=Random) Probability theory and stochastic processes, e.g.:
  - [sum of independent Gaussians](../?module=Random.DistributedSum.of.All_Distributed_Gaussian.All_Indep), [𝒳²(n)](../?module=Random.Distributed_ChiSquared.of.All_Distributed_Gaussian.All_Indep), [Fisher](../?module=Random.Distributed_Fisher.of.All_And_Distributed_Gaussian.Gt_1.Gt_1), [weak law of large numbers](../?module=Random.Lim_ProbLtAbsSubDivSum.eq.One.of.All_EqVar.All_EqExpect.All_Indep.All_MemLp2.All_PSpace), [Cramér](../?module=Random.SatisfiesLDP_EmpiricalMeanLawPi.of.HasFiniteMGF.ForallBddAbove)
  - [naive Bayes document classification](../?module=Random.ArgMax_ProbCond.eq.ArgMax_Mul_Prod_ProbCond.of.NeProbJoint__0.All_CondIndep)
  - [CRF loss function](../?module=Random.All_Eq_AddLogSumExpAdd.All_EqNegLogProb.of.All_Eq_LogProbCond.All_Eq_LogProbCond.Eq_LogProbJoint.All_Lt0ProbJoint.IsDiscreteHMM)
  - [importance-sampled GAE for PPO](../?module=Random.Grad_Expect.eq.Expect_DotPow__Fun_Expect_ArgsIndented.of.All_Eq.All_Or.All_Measurable.LtSup.All_IntegrableFun_SSupProperty_RangeFun_Measure.All_LtSup.LtSup_Integral_SSupProperty_RangeFun_Deriv.All_Differentiable.IsConditionalProbability.SubsetIco)

## arXiv papers

* [Formal Verification of KV-Cache Correctness for Sliding-Window Causal Attention](md/arxiv/kv_cache/main.pdf)
* [Lean 4 Descriptions of Markov Models: from CRF to PPO](md/arxiv/ppo/main.pdf)
* [Fully Radical Solution of the Quartic Equation over ℂ](md/arxiv/quartic_equation/main.pdf)
* [Lean 4-Checked Identities for One-Dimensional Rotary Position Embeddings](md/arxiv/rope/main.pdf)

-------
Plug in a **dynamo for thinking**: state an algorithmic claim as a proposition and prove it one step at a time. The lemmas already in the library can be found and reused, so the same argument does not have to be written out again. Each proof stays in the editor, with its comments, Lean source, and LaTeX shown together.

The library is a searchable Lean 4 reference for students and researchers, for people who design and analyze algorithms, and for anyone reading a formal proof in class or on their own.
<br><br>
