# 什么是lemma.cn
  <br>

[lemma.cn](../index.php)是一个算法形式化定理库网站，最先用[Python](../../py/website/index.php)开发，主要依靠开源符号计算项目 
[sympy](https://github.com/sympy/sympy)进行交互式探索改造, 其函数命名主要参考数学软件语言
[Mathematica](https://reference.wolfram.com/language/index.html.en?source=footer)。后为追求更严密的逻辑完备性，由基于依赖类型理论（DTT）的[Lean](https://github.com/math-proof/lemma/tree/main)证明助手全部改写。 
其主要特征在于：交互式(ITP)、公理化、代码即证明。  
基本设计理念是：语法精确，表达简洁，执行高效，书写美观，力求体现数学美学标准：理论完美性，结构对称性，应用普适性
	
	
* 所述交互式，是指目前做不到全自动定理证明（ATP），而是需要人脑辅助，人通过检索定理库，告诉计算机，面对什么样的题型使用什么样的定理；
* 所述公理化，是指遵循[希尔伯特公理化](https://en.wikipedia.org/wiki/Hilbert%27s_program)思想，所有已证明的数学定理，均由公理模式与推理规则在有限步内导出，在依赖类型理论框架下严格形式化；
* 所述代码即证明，是指基于“柯里-霍华德同构”，将数学命题用[Lean](https://lean-lang.org/)语句精确描述，代码本身就是证明过程，没有自然语言的二义性：显然，同理，易知，一般地，以此类推，反之亦然，综上所述，不失一般性 等证明术语；lean4形式化证明中不存在其它编程语言中浮点数引起的舍入误差问题。  

我们可以在Google搜索引擎中定位到网站信息：[定理库](https://www.google.com.hk/search?q=%E5%AE%9A%E7%90%86%E5%BA%93)。  
参考开源社区中证明助手/定理库：[leanprover](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Algebra/Basic.html)、[coq](https://github.com/coq/coq)和[isabelle](https://isabelle.in.tum.de/)


若要熟练掌握定理推导系统，需要掌握几种常见的推理方法为：  
## 形式化推理策略
1. 归纳法  
归纳法就是数学归纳法，其本质就是从特殊到一般的推理过程: induction 
2. 演绎法  
演绎法是归纳法的逆过程，其本质就是从一般到特殊的推理过程(全称量词消去): specialize/intro/rintro
3. 反证法  
反证法即归谬法，是假设命题为假，基于[排中律](../?module=Bool.Or_Not)，尝试是否能推导出假命题的推理过程: by_contra
4. 分治法  
分治法就是分类讨论法，将一个复杂的问题拆解为若干简单问题的推理过程：by_cases/interval_cases/rcases
5. 溯因法  
溯因法是一种已知结果倒推可能原因的推理方法，由待证命题出发，推导出待证命题为真所需要的充分条件：refine/apply

## 启发式辅助推理
- 类比法  
  (analogy)就是从已知的特殊到未知的特殊的推理方法，比如：尝试将命题从实数域迁移至超实数域，看是否仍然成立。
<br><br>
------


# 算法定理库的建设
  <br>
  
目前积累了<label id=count>5000</label>个已知定理(<label id=lines>100000</label>行lean代码)用于交互式推导。涉及：	
	
* [Bool](../?module=Bool) 初等逻辑(布尔)运算
* [Fin](../?module=Fin) 有限自然数集初等代数
* [Nat](../?module=Nat) 自然数相关初等代数
* [Int](../?module=Int) 整数相关初等代数
* [Rat](../?module=Rat) 有理数相关初等代数
* [Real](../?module=Real) 实数相关代数及实变分析
* [Hyperreal](../?module=Real) 非标准分析
* [Complex](../?module=Complex) 复数相关代数及复变分析
* [Set](../?module=Set) 集合论
* [Finset](../?module=Set) 有限集合论
* [List](../?module=List) 有限列表定理库
* [Vector](../?module=Vector) 一维向量定理库
* [Tensor](../?module=Tensor) 形式化张量演算定理库，概念及其算子与**torch.Tensor**语义上等价，用于深度学习算法形式化验证

<br><br>
-------
该算法形式化定理库可以方便算法研究员分析算法原理，简化论证过程，实现“给思考加上发动机”。主要可以用于理论性数学证明，对数学系学生与研究者，算法工程师、研究员在算法研究，数学分析过程中有一定参考价值，
也可以用于数学工作者整理数学定理知识，通过在线代码编辑器,就可以对定理过程进行编辑，从而完成数学定理的整理工作，并提供快捷方便的功能以便定位定理，函数，符号的定义，通过自然语言注释、Lean4代码与LaTeX公式穿插互译，实现多模态结构化文档呈现，自动生成前端可视化的latex公式，可替代传统纸笔演算。
对于研究和教学都有化繁为简的实用价值，是一本用Lean4语言编写的电子算法参考书。
<br><br>

![](png/national_emblem.png)
[<font size=2>浙公网安备33060202000937号</font>](http://www.beian.gov.cn/portal/registerSystemInfo?recordcode=33060202000937)
[<font size=2>浙ICP备20017509号-3</font>](https://beian.miit.gov.cn/)

<script type=module>
	$('#count').innerHTML = await get("../php/request/count.php");
  $('#lines').innerHTML = await get("../php/request/lines.php");
</script>