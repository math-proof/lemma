# 算法定理库

命题是一条 [Lean](https://lean-lang.org/) 语句，证明是一段能通过类型检查的程序。这就是 *程序即证明*（Curry–Howard 对应）：推导中的空缺不用「显然，易知，同理，一般地，以此类推，反之亦然，综上所述，不失一般性」来填补。实数与超实数按精确语义处理，因此这些证明不带入普通浮点代码的舍入误差。

目前库中收录 <label id=count>5000</label> 条已证定理（<label id=lines>100000</label> 行 Lean 代码），供交互式推导与查阅，覆盖：

* [Bool](../?module=Bool) 命题逻辑与布尔运算
* [Fin](../?module=Fin) 有限索引初等代数
* [Nat](../?module=Nat) 自然数初等代数
* [Int](../?module=Int) 整数初等代数
* [Rat](../?module=Rat) 有理数初等代数
* [Real](../?module=Real) 实分析，例：
  - [Jensen 不等式](../?module=Real.LeSum_Mul.of.EqSumRange__1.All_Ge_0.All_In_Icc.All_Gt0Deriv2.ContinuousOn_Icc)
* [Hyperreal](../?module=Hyperreal) 非标准分析
* [Complex](../?module=Complex) 复分析，例：
  - [一元四次方程](../?module=Complex.Eq0Add_Mul_Pow_4.is.In_Ite_FinsetSSubS__SubS.of.Ne_0)
  - [常系数齐次线性递推通项公式](../?module=Complex.Any_All_Eq_Dot_MulDescFactorial.of.All_Eq_Dot)
  - [梅森定律](../?module=Complex.Eq_Mul_SqrtDiv.of.All_EqDeriv_Mul_ExpMulIArctanDeriv.All_Eq_MulMul_Sin_Cos)
  - [悬链线](../?module=Complex.Any_Eq_AddMul_CoshDivSub.of.All_EqDeriv_Mul_ExpMulIArctanDeriv.ContDiff_2.Differentiable)
* [Set](../?module=Set) 集合论
* [Finset](../?module=Finset) 有限集合论，例：
  - [k-means 聚类](../?module=Finset.LtAddSumS_SquareSub_Div_Sum.of.LtAbsSSub_Div_Sum.NotIn.In.GtCard_0)
* [List](../?module=List) 列表理论
* [Vector](../?module=Vector) 向量（一维张量）理论
* [Matrix](../?module=Matrix) 矩阵理论，例：
  - [置盐定理](../?module=Matrix.Any_And_EqSMul_VecMul_UpdateCol.of.IsIrreducibleUpdateColAdd_Dot.LtDot_Add_SMul.EqSMul.All_Gt_0)
  - [Cholesky 分解](../?module=Matrix.Eq_Mul_Adjoint.of.All_Eq_Ite__Ite_Sqrt_0.All_Lt0Dot_MulVec.EqAdjoint), [PLU 分解](../?module=Matrix.EqMul_T_1.IsLowerTriangular.IsUpperTriangular.EqMulS)
  - [kv_cache](../?module=Matrix.XEq_Append_MulSoftmaxDivMul_AppendTSGetSlice.of.All_XEq_MulSoftmaxAddDivMul_T)
* [Tensor](../?module=Tensor) 形式化张量演算，语义上与 **torch.Tensor** 对齐，用于深度学习算法的形式化表述与验证，例：
  - [旋转位置编码](../?module=Tensor.DotSoftmaxDivDot_Stack_TDot.eq.Stack_Div_SumExp.of.Eq_Stack_Mul)
* [Random](../?module=Random) 概率论与随机过程，例：
  - [独立高斯之和](../?module=Random.DistributedSum.of.All_Distributed_Gaussian.All_Indep)、[𝒳²(n)](../?module=Random.Distributed_ChiSquared.of.All_Distributed_Gaussian.All_Indep)、[Fisher](../?module=Random.Distributed_Fisher.of.All_And_Distributed_Gaussian.Gt_1.Gt_1)、[弱大数定律](../?module=Random.Lim_ProbLtAbsSubDivSum.eq.One.of.All_EqVar.All_EqExpect.All_Indep.All_MemLp2.All_PSpace)、[克拉默](../?module=Random.SatisfiesLDP_EmpiricalMeanLawPi.of.HasFiniteMGF.ForallBddAbove)
  - [朴素贝叶斯文档分类](../?module=Random.ArgMax_ProbCond.eq.ArgMax_Mul_Prod_ProbCond.of.NeProbJoint__0.All_CondIndep)
  - [CRF 损失函数](../?module=Random.All_Eq_AddLogSumExpAdd.All_EqNegLogProb.of.All_Eq_LogProbCond.All_Eq_LogProbCond.Eq_LogProbJoint.All_Lt0ProbJoint.IsDiscreteHMM)
  - [PPO 的重要性采样广义优势估计](../?module=Random.Grad_Expect.eq.Expect_DotPow__Fun_Expect_ArgsIndented.of.All_Eq.All_Or.All_Measurable.LtSup.All_IntegrableFun_SSupProperty_RangeFun_Measure.All_LtSup.LtSup_Integral_SSupProperty_RangeFun_Deriv.All_Differentiable.IsConditionalProbability.SubsetIco)

## arXiv 论文

* [滑动窗口下 KV Cache 正确性的 Lean 4 验证](md/arxiv/kv_cache/滑动窗口下KV%20Cache正确性的Lean4验证.md)
* [Markov 模型的 Lean 4 描述：从 CRF 到 PPO](md/arxiv/ppo/Markov模型的Lean4描述：从CRF到PPO.md)
* [复数域一元四次方程完全根式解](md/arxiv/quartic_equation/复数域一元四次方程完全根式解.md)
* [旋转位置编码 RoPE 的 Lean 4 恒等式验证](md/arxiv/rope/旋转位置编码RoPE的Lean4恒等式验证.md)

-------

**给思考加上发动机**：把算法性质写成命题，再一步一步证明。库中已有的引理可以检索并复用，同一段论证不必反复手写。每份证明留在编辑器里，注释、Lean 源码与 LaTeX 并排呈现。

本库是一部可检索的 Lean 4 参考，面向学生与研究者、从事算法设计与分析的人，以及在课堂或自学中阅读形式化证明的读者。
