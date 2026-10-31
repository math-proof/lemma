# 什么是 lemma.cn
  <br>

[lemma.cn](../index.php) 是一个面向算法的交互式形式化定理库。项目最初以 [Python](../../py/website/index.php) 实现，依托开源符号计算系统 [SymPy](https://github.com/sympy/sympy) 进行交互式探索；函数命名主要参考 [Mathematica](https://reference.wolfram.com/language/index.html.en?source=footer) 的惯例。为获得更高的逻辑严格性与可检验性，核心库现已迁移至基于依赖类型论（DTT）的 [Lean 4](https://github.com/math-proof/lemma/tree/main) 证明助手。

其主要特征可概括为：**交互式证明（ITP）**、**公理化表述**与**程序即证明（Curry–Howard）**。设计目标包括：语法精确、表达简洁、计算可执行、呈现规范，并在形式化表述中尽量体现数学结构的对称性与理论的统一性。

* **交互式**：当前尚不能依赖全自动定理证明（ATP）完成全部工作；证明者需检索定理库，并指导系统选择合适的推理步骤与已有引理。
* **公理化**：在依赖类型论框架下，已证结论由公理模式与推理规则经有限步演绎导出；这一立场受 [希尔伯特形式主义计划](https://en.wikipedia.org/wiki/Hilbert%27s_program) 启发，强调证明的可复核性而非诉诸自然语言中的省略语。
* **程序即证明**：依据 Curry–Howard 同构，命题以 [Lean](https://lean-lang.org/) 语句精确编码，证明即类型正确的程序，从而避免以「显然，易知，同理，一般地，以此类推，反之亦然，综上所述，不失一般性」等自然语言省略语代替可检验的推导；在 Lean 4 的精确实数与超实数语义下，不存在一般数值代码中的浮点舍入误差。


# 算法定理库的建设
  <br>

目前库中收录 <label id=count>5000</label> 条已证定理（<label id=lines>100000</label> 行 Lean 代码），供交互式推导与查阅，覆盖：

* [Bool](../?module=Bool) 命题逻辑与布尔运算
* [Fin](../?module=Fin) 有限索引初等代数
* [Nat](../?module=Nat) 自然数初等代数
* [Int](../?module=Int) 整数初等代数
* [Rat](../?module=Rat) 有理数初等代数
* [Real](../?module=Real) 实分析，例：
  - [Jensen 不等式](../?module=Real.LeSum_Mul.of.EqSumRange__1.All_Ge_0.All_In_Icc.All_Gt0Deriv2.ContinuousOn_Icc)
* [Hyperreal](../?module=Real) 非标准分析
* [Complex](../?module=Complex) 复分析，例：
  - [一元四次方程](../?module=Complex.Eq0Add_Mul_Pow_4.is.In_Ite_FinsetSSubS__SubS.of.Ne_0)
  - [常系数齐次线性递推通项公式](../?module=Complex.Any_All_Eq_Dot_MulDescFactorial.of.All_Eq_Dot)
* [Set](../?module=Set) 集合论
* [Finset](../?module=Finset) 有限集合论，例：
  - [k-means 聚类](../?module=Finset.LtAddSumS_SquareSub_Div_Sum.of.LtAbsSSub_Div_Sum.NotIn.In.GtCard_0)
* [List](../?module=List) 列表理论
* [Vector](../?module=Vector) 向量（一维张量）理论
* [Matrix](../?module=Matrix) 矩阵理论，例：
  - [置盐定理](../?module=Matrix.Any_And_EqSMul_UpdateCol.of.IsIrreducibleUpdateColAdd_Dot.LtDot_Add_SMul.EqSMul.All_Gt_0)
  - [Cholesky 分解](../?module=Finset.All.And.of.Eq_Adjoint.Imp_Gt_0.Eq_Ite.Cholesky)
  - [PLU 分解](../?module=Matrix.EqMul_T_1.IsLowerTriangular.IsUpperTriangular.EqMulS)
* [Tensor](../?module=Tensor) 形式化张量演算，语义上与 **torch.Tensor** 对齐，用于深度学习算法的形式化表述与验证，例：
  - [kv_cache](../?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T)
  - [RoPE](../?module=Tensor.DotSoftmaxDivDot_Stack_TDot.eq.Stack_Div_SumExp.of.Eq_Stack_Mul)
* [Random](../?module=Random) 概率论与随机过程，例：
  - [𝒳²(n)](../?module=Random.Distributed_ChiSquared.of.All_Distributed_Gaussian.All_Indep)、[独立高斯之和](../?module=Random.DistributedSum.of.All_Distributed_Gaussian.All_Indep)、[Fisher](../?module=Random.Distributed_Fisher.of.All_And_Distributed_Gaussian.Gt_1.Gt_1)
  - [朴素贝叶斯文档分类](../?module=Random.ArgMax_ProbCond.eq.ArgMax_Mul_Prod_ProbCond.of.NeProbJoint__0.All_CondIndep)
  - [CRF 损失函数](../?module=Random.All_Eq_AddLogSumExpAdd.All_EqNegLogProb.of.All_Eq_LogProbCond.All_Eq_LogProbCond.Eq_LogProbJoint.All_Lt0ProbJoint.IsDiscreteHMM)、[Viterbi](../?module=Random.All_Eq_Add_MaxAdd.EqMax_ProbJoint.of.All_Eq_LogProbCond.All_Eq_LogProbCond.Eq_LogProbJoint.All_Lt0ProbJoint.IsDiscreteHMM)
  - [GAE（离散）](../?module=Random.GradExpectDotPow_Id.eq.ExpectDot_FunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_NeProb_0.IsPolicyTrajectory.In_Icc.In_Ico)、[GAE（连续）](../?module=Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Icc.In_Ico)

<br><br>
-------

本定理库面向算法与数学形式化研究，可比喻为**给思考加上发动机**：将算法性质表述为可机器检验的命题并逐步完成证明；组织与检索已证引理，缩短手工推导中的重复论证；通过在线编辑器维护证明脚本，并借助注释、Lean 4 源码与 LaTeX 公式的对应呈现，形成结构化文档。

适用对象包括数学及相关方向的学生与研究者、从事算法设计与分析的研究人员，以及需要在教学或自修中查阅形式化证明的读者。本库可视为一部以 Lean 4 写就的、可交互检索的电子算法参考资源。

<br><br>

![](png/national_emblem.png)
[<font size=2>浙公网安备33060202000937号</font>](http://www.beian.gov.cn/portal/registerSystemInfo?recordcode=33060202000937)
[<font size=2>浙ICP备20017509号-3</font>](https://beian.miit.gov.cn/)

<script type=module>
	document.querySelector('#count').innerHTML = await get("../php/request/count.php");
  document.querySelector('#lines').innerHTML = await get("../php/request/lines.php");
</script>
