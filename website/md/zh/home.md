# 什么是 lemma.cn
  <br>

[lemma.cn](../index.php) 是一个面向算法的交互式形式化定理库。项目最初以 [Python](../../py/website/index.php) 实现，依托开源符号计算系统 [SymPy](https://github.com/sympy/sympy) 进行交互式探索；函数命名主要参考 [Mathematica](https://reference.wolfram.com/language/index.html.en?source=footer) 的惯例。为获得更高的逻辑严格性与可检验性，核心库现已迁移至基于依赖类型论（DTT）的 [Lean 4](https://github.com/math-proof/lemma/tree/main) 证明助手。

其主要特征可概括为：**交互式证明（ITP）**、**公理化表述**与**程序即证明（Curry–Howard）**。设计目标包括：语法精确、表达简洁、计算可执行、呈现规范，并在形式化表述中尽量体现数学结构的对称性与理论的统一性。

* **交互式**：当前尚不能依赖全自动定理证明（ATP）完成全部工作；证明者需检索定理库，并指导系统选择合适的推理步骤与已有引理。
* **公理化**：在依赖类型论框架下，已证结论由公理模式与推理规则经有限步演绎导出；这一立场受 [希尔伯特形式主义计划](https://en.wikipedia.org/wiki/Hilbert%27s_program) 启发，强调证明的可复核性而非诉诸自然语言中的省略语。
* **程序即证明**：依据 Curry–Howard 同构，命题以 [Lean](https://lean-lang.org/) 语句精确编码，证明即类型正确的程序，从而避免以「显然，易知，同理，一般地，以此类推，反之亦然，综上所述，不失一般性」等自然语言省略语代替可检验的推导；在 Lean 4 的精确实数与超实数语义下，不存在一般数值代码中的浮点舍入误差。

网站可通过 google/baidu/bing 检索「定理库」访问。相关开源证明助手与定理库包括 [Lean/mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Algebra/Basic.html)、[Coq](https://github.com/coq/coq) 与 [Isabelle](https://isabelle.in.tum.de/)。

熟练使用本系统，通常需要熟悉下列推理模式及其在 Lean 中的对应策略：

## 形式化推理策略

1. **归纳法**  
   数学归纳法：由基例与归纳步建立对全体自然数（或良基结构）的命题，如：`induction`
2. **演绎法**  
   由一般命题推出特殊实例，含全称量词引入与消去，如：`specialize` / `intro` / `rintro`
3. **反证法**  
   归谬法：假设结论否定成立，据 [排中律](../?module=Bool.Or_Not) 推导矛盾，如：`by_contra`
4. **分治法**  
   分类讨论：将目标分解为互斥且穷尽的情形分别证明，如：`by_cases` / `interval_cases` / `rcases`
5. **溯因式推理**  
   由待证目标反向寻找充分条件或适用引理（证明搜索意义上的“由果索因”），如：`refine` / `apply`

## 启发式辅助推理

- **类比**  
  在保持结构的前提下，将已知结论从某一数学结构迁移至另一结构（例如由实数域推广至超实数域），以检验命题是否仍成立。

<br><br>
------


# 算法定理库的建设
  <br>

目前库中收录 <label id=count>5000</label> 条已证定理（<label id=lines>100000</label> 行 Lean 代码），供交互式推导与查阅，覆盖：

* [Bool](../?module=Bool) 命题逻辑与布尔运算
* [Fin](../?module=Fin) 有限索引初等代数
* [Nat](../?module=Nat) 自然数初等代数
* [Int](../?module=Int) 整数初等代数
* [Rat](../?module=Rat) 有理数初等代数
* [Real](../?module=Real) 实分析
* [Hyperreal](../?module=Real) 非标准分析
* [Complex](../?module=Complex) 复分析，例：
  - [一元二次方程](../?module=Complex.Eq0Add_Mul_Square.is.In_FinsetDivS_Mul2.of.Ne_0)
  - [一元三次方程](../?module=Complex.Eq0Add_Mul_Pow_3.is.In_Finset_SubSAddMulS.of.Ne_0)
  - [一元四次方程](../?module=Complex.Eq0Add_Mul_Pow_4.is.In_Ite_FinsetSSubS__SubS.of.Ne_0)
* [Set](../?module=Set) 集合论
* [Finset](../?module=Set) 有限集合论
* [List](../?module=List) 列表理论
* [Vector](../?module=Vector) 向量（一维张量）理论
* [Tensor](../?module=Tensor) 形式化张量演算，语义上与 **torch.Tensor** 对齐，用于深度学习算法的形式化表述与验证，例：
  - [kv_cache](../?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T)

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
