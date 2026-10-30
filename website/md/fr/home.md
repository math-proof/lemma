# Qu'est-ce que lemma.cn
  <br>

[lemma.cn](../index.php) est une bibliothèque interactive de théorèmes formalisés pour les algorithmes. Le projet a d'abord été développé en [Python](../../py/website/index.php), avec le système de calcul symbolique open source [SymPy](https://github.com/sympy/sympy) pour l'exploration interactive ; la nomenclature des fonctions s'inspire surtout des conventions de [Mathematica](https://reference.wolfram.com/language/index.html.en?source=footer). Pour une rigueur logique et une vérifiabilité accrues, le cœur de la bibliothèque a été migré vers l'assistant de preuve [Lean 4](https://github.com/math-proof/lemma/tree/main), fondé sur la théorie des types dépendants (DTT).

Ses traits principaux se résument ainsi : **preuve interactive (ITP)**, **axiomatisation** et **programme comme preuve (Curry–Howard)**. Les objectifs de conception incluent une syntaxe précise, une expression concise, une exécution effective et une présentation claire, en mettant en valeur la symétrie des structures mathématiques et l'unité de la théorie.

* **Interactive** : on ne peut pas encore s'appuyer sur la preuve automatique des théorèmes (ATP) pour tout ; le démonstrateur consulte la bibliothèque et guide le système dans le choix des étapes et des lemmes existants.
* **Axiomatisation** : dans le cadre de la théorie des types dépendants, chaque résultat établi se déduit en un nombre fini d'étapes à partir de schémas d'axiomes et de règles d'inférence ; cette orientation, inspirée du [programme formaliste de Hilbert](https://en.wikipedia.org/wiki/Hilbert%27s_program), privilégie la reproductibilité des preuves plutôt que les raccourcis du langage naturel.
* **Programme comme preuve** : par l'isomorphisme de Curry–Howard, les propositions sont codées exactement en [Lean](https://lean-lang.org/) ; la preuve est un programme bien typé, sans recourir à des formules du type « évidemment », « il est facile de voir », « de même », « en général », « et ainsi de suite », « réciproquement », « pour conclure », « sans perte de généralité » à la place d'un enchaînement vérifiable ; sous la sémantique exacte des réels et hyperréels de Lean 4, il n'y a pas d'erreur d'arrondi en virgule flottante comme dans le code numérique ordinaire.


# Construction de la bibliothèque algorithmique
  <br>

La bibliothèque contient <label id=count>5000</label> théorèmes établis (<label id=lines>100000</label> lignes de code Lean), disponibles pour la dérivation interactive et la consultation. Domaines principaux :

* [Bool](../?module=Bool) Logique propositionnelle et opérations booléennes
* [Fin](../?module=Fin) Algèbre élémentaire sur des indices finis
* [Nat](../?module=Nat) Algèbre élémentaire des entiers naturels
* [Int](../?module=Int) Algèbre élémentaire des entiers relatifs
* [Rat](../?module=Rat) Algèbre élémentaire des rationnels
* [Real](../?module=Real) Algèbre et analyse réelle, p. ex. :
  - [inégalité de Jensen](../?module=Real.LeSum_Mul.of.EqSumRange__1.All_Ge_0.All_In_Icc.All_Gt0Deriv2.ContinuousOn_Icc.main)
* [Hyperreal](../?module=Real) Analyse non standard
* [Complex](../?module=Complex) Analyse complexe, p. ex. :
  - [équation quartique](../?module=Complex.Eq0Add_Mul_Pow_4.is.In_Ite_FinsetSSubS__SubS.of.Ne_0)
  - [forme fermée d'une récurrence linéaire homogène à coefficients constants](../?module=Complex.Any_All_Eq_Dot_MulDescFactorial.of.All_Eq_Dot)
* [Set](../?module=Set) Théorie des ensembles
* [Finset](../?module=Finset) Ensembles finis, p. ex. :
  - [clustering k-means](../?module=Finset.LeAddSumS_SquareSub_Div_Sum.of.LeAbsSSub_Div_Sum.NotIn.In.GtCard_0)
* [List](../?module=List) Théorie des listes
* [Vector](../?module=Vector) Vecteurs (tenseurs unidimensionnels)
* [Matrix](../?module=Matrix) Théorie des matrices, p. ex. :
  - [théorème d'Okishio](../?module=Matrix.Any_And_EqSMul_UpdateCol.of.IsIrreducibleUpdateColAdd_Dot.LtDot_Add_SMul.EqSMul.All_Gt_0)
  - [décomposition de Cholesky](../?module=Finset.And.of.Eq_Adjoint.Imp_Gt_0.Eq_Ite.Cholesky)
  - [décomposition PLU](../?module=Tensor.Eq.Dot.PLU.of.Eq.Eq_Dot.Eq_Ite)
* [Tensor](../?module=Tensor) Calcul tensoriel formalisé, sémantiquement aligné sur **torch.Tensor**, pour la spécification et la vérification formelle d'algorithmes d'apprentissage profond, p. ex. :
  - [kv_cache](../?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T)
  - [RoPE](../?module=Tensor.DotSoftmaxDivDot_Stack_TDot.eq.Stack_Div_SumExp.of.Eq_Stack_Mul)
* [Random](../?module=Random) Probabilités et processus stochastiques, p. ex. :
  - [𝒳²(n)](../?module=Random.Distributed.ChiSquared.of.All_Distributed_Gaussian.All_Indep), [somme de gaussiennes indépendantes](../?module=Random.DistributedSum.of.All_Distributed_Gaussian.All_Indep)
  - [classification de documents naïve bayésienne](../?module=Random.ArgMax_ProbCond.eq.ArgMax_Mul_Prod_ProbCond.of.NeProbJoint__0.All_CondIndep)
  - [fonction de perte CRF](../?module=Random.All_Eq_AddLogSumExpAdd.All_EqNegLogProb.of.All_Eq_LogProbCond.All_Eq_LogProbCond.Eq_LogProbJoint.All_Lt0ProbJoint.IsDiscreteHMM), [Viterbi](../?module=Random.All_Eq_Add_MaxAdd.EqMax_ProbJoint.of.All_Eq_LogProbCond.All_Eq_LogProbCond.Eq_LogProbJoint.All_Lt0ProbJoint.IsDiscreteHMM)
  - [GAE (discret)](../?module=Random.GradExpectDotPow_Id.eq.ExpectDot_FunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_NeProb_0.IsPolicyTrajectory.In_Icc.In_Ico), [GAE (continu)](../?module=Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Icc.In_Ico)

<br><br>
-------

Cette bibliothèque s'adresse à la recherche en algorithmique et en formalisation mathématique — une métaphore de **dynamo pour la pensée**: formuler les propriétés algorithmiques comme propositions vérifiables par machine et les prouver pas à pas ; organiser et retrouver les lemmes pour raccourcir les arguments manuels répétitifs ; maintenir les scripts de preuve dans l'éditeur en ligne, avec commentaires, source Lean 4 et formules LaTeX présentés de façon structurée.

Elle s'adresse aux étudiants et chercheurs en mathématiques et domaines voisins, aux concepteurs et analystes d'algorithmes, ainsi qu'aux lecteurs qui consultent des preuves formalisées pour l'enseignement ou l'autoformation. La bibliothèque constitue une référence algorithmique électronique, interactive et consultable, rédigée en Lean 4.

<br><br>

![](png/national_emblem.png)
[<font size=2>浙公网安备33060202000937号</font>](http://www.beian.gov.cn/portal/registerSystemInfo?recordcode=33060202000937)
[<font size=2>浙ICP备20017509号-3</font>](https://beian.miit.gov.cn/)

<script type=module>
	document.querySelector('#count').innerHTML = await get("../php/request/count.php");
  document.querySelector('#lines').innerHTML = await get("../php/request/lines.php");
</script>
