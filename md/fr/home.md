# Répertoire de théorèmes algorithmiques

Un énoncé est une proposition [Lean](https://lean-lang.org/), et sa preuve est un programme qui passe le contrôle de types. C'est le *programme comme preuve*, au sens de la correspondance de Curry–Howard : un trou ne se comble pas par « évidemment », « il est facile de voir » ou « sans perte de généralité ». Les réels et les hyperréels sont exacts, donc ces preuves n'héritent pas des arrondis du code en virgule flottante.

La bibliothèque contient <label id=count>5000</label> théorèmes établis (<label id=lines>100000</label> lignes de code Lean), disponibles pour la dérivation interactive et la consultation. Domaines principaux :

* [Bool](../?module=Bool) Logique propositionnelle et opérations booléennes
* [Fin](../?module=Fin) Algèbre élémentaire sur des indices finis
* [Nat](../?module=Nat) Algèbre élémentaire des entiers naturels
* [Int](../?module=Int) Algèbre élémentaire des entiers relatifs
* [Rat](../?module=Rat) Algèbre élémentaire des rationnels
* [Real](../?module=Real) Algèbre et analyse réelle, p. ex. :
  - [inégalité de Jensen](../?module=Real.LeSum_Mul.of.EqSumRange__1.All_Ge_0.All_In_Icc.All_Gt0Deriv2.ContinuousOn_Icc)
* [Hyperreal](../?module=Hyperreal) Analyse non standard
* [Complex](../?module=Complex) Analyse complexe, p. ex. :
  - [équation quartique](../?module=Complex.Eq0Add_Mul_Pow_4.is.In_Ite_FinsetSSubS__SubS.of.Ne_0)
  - [forme fermée d'une récurrence linéaire homogène à coefficients constants](../?module=Complex.Any_All_Eq_Dot_MulDescFactorial.of.All_Eq_Dot)
  - [loi de Mersenne](../?module=Complex.Eq_Mul_SqrtDiv.of.All_EqDeriv_Mul_ExpMulIArctanDeriv.All_Eq_MulMul_Sin_Cos)
  - [chaînette](../?module=Complex.Any_Eq_AddMul_CoshDivSub.of.All_EqDeriv_Mul_ExpMulIArctanDeriv.ContDiff_2.Differentiable)
* [Set](../?module=Set) Théorie des ensembles
* [Finset](../?module=Finset) Ensembles finis, p. ex. :
  - [clustering k-means](../?module=Finset.LtAddSumS_SquareSub_Div_Sum.of.LtAbsSSub_Div_Sum.NotIn.In.GtCard_0)
* [List](../?module=List) Théorie des listes
* [Vector](../?module=Vector) Vecteurs (tenseurs unidimensionnels)
* [Matrix](../?module=Matrix) Théorie des matrices, p. ex. :
  - [théorème d'Okishio](../?module=Matrix.Any_And_EqSMul_VecMul_UpdateCol.of.IsIrreducibleUpdateColAdd_Dot.LtDot_Add_SMul.EqSMul.All_Gt_0)
  - [décomposition de Cholesky](../?module=Matrix.Eq_Mul_Adjoint.of.All_Eq_Ite__Ite_Sqrt_0.All_Lt0Dot_MulVec.EqAdjoint), [décomposition PLU](../?module=Matrix.EqMul_T_1.IsLowerTriangular.IsUpperTriangular.EqMulS)
  - [kv_cache](../?module=Matrix.XEq_Append_MulSoftmaxDivMul_AppendTSGetSlice.of.All_XEq_MulSoftmaxAddDivMul_T)
* [Tensor](../?module=Tensor) Calcul tensoriel formalisé, sémantiquement aligné sur **torch.Tensor**, pour la spécification et la vérification formelle d'algorithmes d'apprentissage profond, p. ex. :
  - [Plongement positionnel rotatif](../?module=Tensor.DotSoftmaxDivDot_Stack_TDot.eq.Stack_Div_SumExp.of.Eq_Stack_Mul)
* [Random](../?module=Random) Probabilités et processus stochastiques, p. ex. :
  - [somme de gaussiennes indépendantes](../?module=Random.DistributedSum.of.All_Distributed_Gaussian.All_Indep), [𝒳²(n)](../?module=Random.Distributed_ChiSquared.of.All_Distributed_Gaussian.All_Indep), [Fisher](../?module=Random.Distributed_Fisher.of.All_And_Distributed_Gaussian.Gt_1.Gt_1), [loi faible des grands nombres](../?module=Random.Lim_ProbLtAbsSubDivSum.eq.One.of.All_EqVar.All_EqExpect.All_Indep.All_MemLp2.All_PSpace), [Cramér](../?module=Random.SatisfiesLDP_EmpiricalMeanLawPi.of.HasFiniteMGF.ForallBddAbove)
  - [classification de documents naïve bayésienne](../?module=Random.ArgMax_ProbCond.eq.ArgMax_Mul_Prod_ProbCond.of.NeProbJoint__0.All_CondIndep)
  - [fonction de perte CRF](../?module=Random.All_Eq_AddLogSumExpAdd.All_EqNegLogProb.of.All_Eq_LogProbCond.All_Eq_LogProbCond.Eq_LogProbJoint.All_Lt0ProbJoint.IsDiscreteHMM)
  - [GAE à échantillonnage d'importance pour PPO](../?module=Random.Grad_Expect.eq.Expect_DotPow__Fun_Expect_ArgsIndented.of.All_Eq.All_Or.All_Measurable.LtSup.All_IntegrableFun_SSupProperty_RangeFun_Measure.All_LtSup.LtSup_Integral_SSupProperty_RangeFun_Deriv.All_Differentiable.IsConditionalProbability.SubsetIco)

## Articles arXiv

* [Formal Verification of KV-Cache Correctness for Sliding-Window Causal Attention](md/arxiv/kv_cache/main.pdf)
* [Lean 4 Descriptions of Markov Models: from CRF to PPO](md/arxiv/ppo/main.pdf)
* [Fully Radical Solution of the Quartic Equation over ℂ](md/arxiv/quartic_equation/main.pdf)
* [Lean 4-Checked Identities for One-Dimensional Rotary Position Embeddings](md/arxiv/rope/main.pdf)

-------

Brancher une **dynamo pour la pensée** : énoncer une propriété algorithmique comme proposition, puis la prouver pas à pas. Les lemmes déjà dans la bibliothèque se retrouvent et se réutilisent, sans réécrire le même argument. Chaque preuve reste dans l'éditeur, avec ses commentaires, le source Lean et le LaTeX présentés ensemble.

La bibliothèque est une référence Lean 4 consultable, pour les étudiants et les chercheurs, pour qui conçoit et analyse des algorithmes, et pour qui lit une preuve formalisée en cours ou en autodidacte.
