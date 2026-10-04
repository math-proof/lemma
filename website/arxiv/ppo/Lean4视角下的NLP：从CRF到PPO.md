项目工件：[math-proof/lemma](https://github.com/math-proof/lemma)

Markov 乘积：[crf.markov](http://www.lemma.cn/lean/?module=Random.ProbJoint.eq.Mul_Prod_MulProbSCond.of.All_CondIndep.All_CondIndep.EqMeasure_Count.EqMeasure_Count.All_Measurable.All_Measurable)，前向递推与负对数似然：[y_given_x](http://www.lemma.cn/lean/?module=Tensor.Imp_Eq_Add_LogSumExp.EqNegLogProb.of.Ne0ProbJoint.Indep.y_given_x)，Viterbi：[crf.viterbi](http://www.lemma.cn/lean/?module=Tensor.And.of.Ne_0.Eq.Eq.Eq)，前向--后向：[forward_backward](http://www.lemma.cn/lean/?module=Tensor.And.of.All_Eq_Sum_Mul.All_Eq_1.All_Eq_Mul.All_Eq.forward_backward)

Bellman：[Bellman](http://www.lemma.cn/lean/?module=Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman)，REINFORCE：[Lean 4](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.IsFinite.policy_gradient_theorem)

无偏优势估计：[Lean 4](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.unbiased_advantage_estimate)，广义优势估计：[Lean 4](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.generalized_advantage_estimate)

# 摘要

线性链条件随机场（CRF）用于序列标注，近端策略优化（PPO）用于带反馈的强化学习，乍看是 NLP 里互不相干的两个角落。我们围绕三个结果组织一份 Lean 4 的说明：线性链 CRF 的前向与后向传播、Bellman 方程，以及策略梯度定理及其 REINFORCE 与广义优势估计（GAE）形式。三者依赖同一个装置：马尔可夫结构把对指数多条路径（或无穷视野）的求和变成一步递推，对 CRF 配分函数是前向地跑，对后缀和与价值函数是后向地跑。我们明确说出哪些被 Lean 4 + mathlib 机器检查过。

CRF 一侧，我们形式化了：Markov 乘积、对数得分分解为转移项与发射项、log-sum-exp 形式的前向递推及 \(-\log p(y\mid x)=\log Z(x)-\text{score}(x,y)\)、Viterbi 的 max-plus 递推（只有最大值），以及一个对任意实权重链成立的前向--后向定理：前向递推、后向递推、经过时刻 \(t\) 的标签 \(a\) 的全部路径的总权重恒等式 \(\sum_{ys:\,ys_t=a}P_m(ys)=z_t(a)\,\beta_t(a)\)，以及 \(Z\) 与切分点 \(t\) 无关。强化学习一侧，我们形式化了状态与动作空间有限的折扣马尔可夫决策过程（MDP）及其轨迹测度、Bellman 方程、对时间跨度归纳的策略梯度定理（截断、动作价值与 REINFORCE 三种形式）、使基线消失的零均值得分恒等式、无偏折扣优势估计，以及对精确价值函数、所有 \(\lambda\in[0,1]\) 的 GAE。

没有形式化、并且明确标出的有：归一化的后验边缘与成对边缘、恒等式 \(\nabla\log Z=\mathbb E[\nabla\,\text{score}]\)、Viterbi 的 argmax，以及 PPO 算法的每个成分（裁剪替代目标、重要性比、KL 与价值裁剪、学习得到的 critic）；前向、后向与 Bellman 递推之间的类比，以及序列标注与序列到序列生成的对比，是概念性的，不是 Lean 定理。所有已检查的定理只依赖 `propext`、`Classical.choice`、`Quot.sound` 三条公理。

# 1 引言

用线性链 CRF [10][28] 做序列标注，与用 PPO [25][32][19] 做基于人类反馈的强化学习（RLHF），通常被放在不同的章节里讲。前者是监督学习：已观测的句子 \(x\) 被映射成同样长度的标签序列 \(y\)，目标是最大化 \(\log p(y\mid x)\)。后者是强化学习算法：语言模型逐个生成词元，标量奖励评判整段文本，策略用裁剪的策略梯度步更新。本文讨论两者共有什么，依据是我们在 `lemma` 库 [15] 里，用 Lean 4 [6] 和 [mathlib](https://leanprover-community.github.io/mathlib4_docs/) [16][17] 已经证明了什么。

**三个核心主题。** 本文围绕三个结果组织，每个都有自己的一节和自己的 Lean 陈述。

1. **线性链 CRF 的前向与后向传播**（第 5 节）。前向递推 \(z_{t+1}(a)=\sum_bz_t(b)\,\psi_{t+1}(b,a)\) 用 \(O(mk^2)\) 次运算算出配分函数 \(Z\)，而不是对 \(k^{m+1}\) 条标签路径求和；后向递推 \(\beta_t(a)=\sum_c\psi_{t+1}(a,c)\,\beta_{t+1}(c)\) 概括后缀，\(z_t(a)\beta_t(a)\) 是经过时刻 \(t\) 的标签 \(a\) 的全部标签路径的总权重，即后验边缘分布的分子。Lean 里有：隐马尔可夫条件情形的、满足 \(-\log p(y\mid x)=\log Z-\text{score}\) 的前向递推，Viterbi 的数值递推，以及对任意权重链成立的前向--后向定理（定理 5.4）。
2. **Bellman 方程**（第 6 节）。对状态与动作空间有限的折扣 MDP，价值函数满足 \(V_t(s_t)=\mathbb E[{\color{red}r}_t+\gamma V_{t+1}({\color{magenta}s}_{t+1})\mid{\color{red}s}_t=s_t]\)，动作价值 \(Q_t\) 同理；Lean 对 MDP 的轨迹测度证明了这一点。
3. **策略梯度定理、REINFORCE 与 GAE**（第 7 节）。\(\nabla\mathbb E[\sum_t{}'\,\gamma^t{\color{red}r}_t]=\mathbb E[\sum_t{}'\,\gamma^tG_t\nabla\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)]\) 由对时间跨度的归纳证明，带有显式余项的有限视野恒等式；把 \(G_t\) 换成无偏优势，或换成由精确价值函数构造的广义优势 \(\hat A^\lambda_t\)，梯度不变。

第 8 节说明 PPO 的哪些部分落在这些陈述之外；第 9 节是序列标注对序列到序列生成的简短概念性对比，不是定理。

**共同的线索。** 本文每个模型里，长度为 \(n\) 的对象的概率都是单步因子的乘积（马尔可夫假设），所以它的对数是逐步项之和：CRF 得分、轨迹的对数概率、语言模型下句子的对数似然。由此用到两个推论。第一，对指数多条路径的求和可以用一步递推计算：CRF 的前向与后向递推是 sum-product 动态规划（Viterbi 是它的 max-sum 版本），Bellman 递推是同样形状的期望递推，沿时间向后跑（第 6.3 节）。我们把这当作类比，而不是定理：没有任何 Lean 陈述把 CRF 递推与 Bellman 递推联系起来。第二，当每个单步因子的和为 1 时，\(\sum_ap(a)=1\) 蕴含 \(\mathbb E_{a\sim p}[\nabla\log p(a)]=0\)，这正是策略梯度可以减去基线而不改变的原因（第 7.2 节）。

**贡献。**

1. CRF 传播（第 4、5 节）：Markov 乘积 [crf.markov](http://www.lemma.cn/lean/?module=Random.ProbJoint.eq.Mul_Prod_MulProbSCond.of.All_CondIndep.All_CondIndep.EqMeasure_Count.EqMeasure_Count.All_Measurable.All_Measurable)，对数得分 [crf.markov.logits](http://www.lemma.cn/lean/?module=Tensor.Eq.of.Ne_0.Eq.Eq.Eq.Eq_log.Eq_log.Eq_log) 与 [crf.logits](http://www.lemma.cn/lean/?module=Tensor.Imp.of.Eq)，满足 \(-\log p(y\mid x)=\log Z-\text{score}\) 的前向递推 [y_given_x](http://www.lemma.cn/lean/?module=Tensor.Imp_Eq_Add_LogSumExp.EqNegLogProb.of.Ne0ProbJoint.Indep.y_given_x)，Viterbi 数值递推 [crf.viterbi](http://www.lemma.cn/lean/?module=Tensor.And.of.Ne_0.Eq.Eq.Eq)，以及新的前向--后向定理 [crf.forward_backward](http://www.lemma.cn/lean/?module=Tensor.And.of.All_Eq_Sum_Mul.All_Eq_1.All_Eq_Mul.All_Eq.forward_backward)，其假设恰是一步前缀分解与后向递推（定理 5.4）。
2. Bellman 方程 [Bellman](http://www.lemma.cn/lean/?module=Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman)，建立在轨迹层面的 MDP 上，其轨迹律的马尔可夫性是已证明的（`joint_succ`、`hist_step`）（第 6 节）。
3. 对时间跨度归纳证明的策略梯度定理，截断、动作价值与 REINFORCE 三种形式（[policy_gradient_theorem](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.IsFinite.policy_gradient_theorem)）；无偏优势估计 [unbiased_advantage_estimate](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.unbiased_advantage_estimate)；以及对精确价值函数、所有 \(\lambda\in[0,1]\) 的 GAE [generalized_advantage_estimate](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.generalized_advantage_estimate) 及其加权平均形式（第 7 节）。
4. 明确写出什么**没有**覆盖，特别是 PPO 的各个成分（第 8、12 节），以及两张对比表（第 10 节）。

库里为极限、期望与概率设计的教科书语法糖，让 Lean 陈述读起来像论文里的公式，在第 3 节概述。

**诚实的范围说明。**（i）下游的对数域 CRF 引理（logits、带负对数似然的前向递推、Viterbi）把一步前缀分解当作**假设**；其概率版本由发射与一阶马尔可夫两条条件独立推出（定理 4.3），但没有从模型的具体构造推出它。（ii）后向递推只在前向--后向定理（定理 5.4）之内被形式化，它是关于任意实权重的陈述：没有把 CRF 分布 \(p(y\mid x)=\prod_t\psi_t/Z\) 定义为模型，归一化的后验边缘、成对边缘、恒等式 \(\nabla\log Z=\mathbb E[\nabla\,\text{score}]\)，以及带回溯指针的 Viterbi argmax **没有**形式化。（iii）没有序列到序列、教师强制、exposure bias 或 label bias 的引理。（iv）MDP 被形式化了，PPO 没有：没有裁剪替代目标、重要性比、KL 惩罚、价值裁剪、学习得到的 critic，也没有单调改进或收敛陈述。（v）GAE 只对精确价值函数证明，状态与动作空间有限，奖励有界，\(\gamma<1\)。第 6.3 节、第 9 节和第 10 节是概念性对比，文中已标明。

# 2 相关工作

**HMM、MEMM 与 CRF。** 隐马尔可夫模型（HMM）[21] 是生成式的：它对联合分布 \(p(x,y)=\prod_tp(y_t\mid y_{t-1})\,p(x_t\mid y_t)\) 建模，各因子局部归一化。最大熵马尔可夫模型（MEMM）[18] 是判别式的，但仍是局部归一化，\(\prod_tp(y_t\mid y_{t-1},x)\)，并有 label bias 问题；条件随机场 [10] 用一个对整条标签序列的配分函数 \(Z(x)\) 做全局归一化，去掉了这个问题。Sutton 与 McCallum [28] 给出了标准的教程式处理，包括前向、后向与 Viterbi 递推。神经 CRF 把神经网络放在一元得分之下：Collobert 等人 [5] 用带转移得分的句子级似然训练，Huang 等人 [8]、Lample 等人 [11] 与 Ma 与 Hovy [14] 在 BiLSTM 编码器上加 CRF 层，Andor 等人 [1] 主张全局归一化的基于转移的神经网络。苏剑林在“科学空间”的博客文章给出了简明的中文推导：CRF 损失及其递归的归一化项 [27]；面向 NER 的、可替代 CRF 的基于片段的方法是 GlobalPointer [29]；更多与 CRF 相关的文章列在站点的[搜索页](https://spaces.ac.cn/search/CRF/) [30]。

**序列到序列模型与 exposure bias。** 神经序列到序列模型 [31][2][36] 把 \(p(y\mid x)=\prod_tp(y_t\mid x,y_{<t})\) 分解开，训练时用真实前缀（教师强制），解码时却用自己生成的前缀；这个不匹配叫 exposure bias，对策有 scheduled sampling [3]、序列级训练 [22] 与 beam-search 优化 [38]。第 9 节有一个小例子：更大的 beam 返回的序列反而更好。

**策略梯度、GAE 与 PPO。** 策略梯度定理出自 Sutton 等人 [33]，似然比估计与强化基线来自 Williams [37]；Greensmith、Bartlett、Baxter [7] 把基线当作方差缩减手段做了分析。Schulman 等人 [23] 提出 GAE，当时与信赖域策略优化（TRPO）[24] 配合使用；TRPO 早于 GAE，并没有定义它。PPO [25] 用裁剪的替代目标取代信赖域约束，并用截断（有限视野）的 GAE 计算优势，即其公式 (10)–(11)。语言模型的 RLHF [32][19] 在词元上运行 PPO，使用奖励模型得分和对参考模型的 KL 惩罚，GRPO [26] 是去掉学习得到的 critic 的 PPO 变体。有限 MDP 的标准参考文献是 Puterman [20] 以及 Sutton 与 Barto [34]。

**形式化方面。** CertRL [35] 在 Coq 里形式化了值迭代与策略迭代的收敛，[Chevallier 与 Fleuriot](https://arxiv.org/abs/2112.05996) [4] 在 Isabelle/HOL 里形式化了带奖励的有限 MDP，包括 Bellman 方程、\(\gamma<1\) 时最优策略的存在性，以及值迭代与策略迭代；两者都没有涉及策略梯度。在 Lean 4 里，[TorchLean](https://github.com/lean-dojo/TorchLean) [13] 证明了关于 MDP 与 Bellman 算子的结构性和动态规划性质，并含有策略梯度与 PPO 的训练代码，但没有策略梯度定理。与第 7 节最接近的是 Zhang 的 `rl-theory-in-lean` 中的 `PolicyGradient` 模块 [rl-theory-in-lean](https://github.com/ShangtongZhang/rl-theory-in-lean/commit/2a9d01a236961b1c9bc451a8926346364fc66e7f) [39]，这是一套实验性的、主要由机器生成的开发（其提交与 AI 助手共同署名），2026 年 3 月提交，后来从该项目的 main 分支撤回，在所引用的提交处仍可访问。对有限的状态和动作空间、带有限个实参数的策略，它证明了占用测度形式

\[
\nabla_\theta J(\theta)=(1-\gamma)^{-1}\sum_{s,a}d^{\pi_\theta}(s)\,\pi_\theta(a\mid s)\,Q^{\pi_\theta}(s,a)\,\nabla_\theta\log\pi_\theta(a\mid s),
\]

方法是 Banach 不动点加 Neumann 级数，要求策略严格为正，没有轨迹、回报或优势。我们的在轨迹层面：轨迹律是 mathlib 的 `Kernel.trajMeasure` [16]（Ionescu-Tulcea 定理的实现 [9]），价值函数是条件期望，并且先沿教科书推导 [40, 第 13.2 节] 用归纳法证出精确的有限视野恒等式，再取极限。据我们所知（基于对 GitHub、arXiv 与网络的搜索），这是第一个沿教科书推导路线的 Lean 4 证明；两者只共享教科书的起点（[33] 的一步递推与对数导数技巧），我们的证明是独立完成的。我们不知道此前有关于 CRF 前向或后向递推的 Lean 4 形式化。

# 3 Lean 记号简述

下面的陈述用库里的**教科书语法糖**书写：这是一种表层写法，把冗长的测度论或滤子表达式压缩成接近教科书的形式，同时展开为完整的、可机器检查的定义，不引入新公理（“语法糖”这一通用术语源自 Landin [12]）。这里只回顾后文用到的部分。

| Lean 写法 | 含义 |
|---|---|
| `lim [n → ∞] e = a` | `Filter.Tendsto (fun n => e) atTop (nhds a)`；始终是等式形式，断言收敛 |
| `𝔼[x: π](f x \| y = y0)` | \(\mathbb E_\pi[f(x)\mid y=y_0]\)，mathlib 条件测度下的期望；零概率事件上为 \(0\) |
| `ℙ[π](x = x0 \| y = y0)` | \(\mathbb P_\pi(x=x_0\mid y=y_0)\)（相对计数测度的密度即概率质量） |
| `x[:n]` | 随机向量 \((x_0,\dots,x_{n-1})\)；对普通序列 `f[:n]` 是 \((f_0,\dots,f_{n-1})\) |
| `(ℙ[π](…) : ℝ).log` | \(\log\mathbb P_\pi(\dots)\)（从 \([0,\infty]\) 到 \(\mathbb R\) 的受限强制转换不是全局实例） |
| `∇[θ] e`、`sup[x] e < ∞` | \(\nabla_\theta e\)（Fréchet 导数的 Riesz 表示元）；\(e\) 有上界 |
| `max[ys : Fin t → Y] f ys`、`v.exp.sum.log` | 有限指标类型上的 \(\max_{ys}f(ys)\)；\(\log\sum_be^{v_b}\)（`v.exp`、`v.sum`、`v.max` 逐点作用或对向量归约） |

**颜色。** lemma.cn 的渲染器把每条陈述排成 LaTeX，并按概率角色给标识符上色：{\color{red}红色}是随机变量（样本空间上的函数、\(\mathbb E\) 绑定式里被积掉的变量、\(\mathbb P\) 事件里 `=` 左边的变量），{\color{magenta}品红}是随机自变量（作为函数自变量的随机变量，使整个表达式本身是随机的），黑色是观测值。我们沿用这一约定：\({\color{red}s}_t,{\color{red}a}_t,{\color{red}r}_t\) 是红色，\(s_t,a_t,x,u,y\) 是取值。

**零概率事件与极限。** 由于 \(\mu[\,\cdot\mid B]=\mu(B)^{-1}\mu|_B\) 在 \(\mu(B)=0\) 时是零测度，在不可达状态上的条件期望是 \(0\)；因此关于价值函数的假设限制在**可达**取值 \(s_t\)，即 \(\mathbb P_\theta({\color{red}s}_t=s_t)\ne0\) 的那些。无穷和是 Lean 的 `tsum`（可和族的和，否则为 \(0\)），每个极限都是显式的 `Filter.Tendsto` 陈述。我们陈述的唯一极限引理如下，用于截断策略梯度的余项（第 7 节）。

**引理 3.1（[Lim.of.LtAbs.IsFinite](http://www.lemma.cn/lean/?module=Real.Eq_0.Lim.of.LtAbs.IsFinite)）。** 设 \(\gamma\in\mathbb R\)，\(x:\mathbb N\to\mathbb R\)，\(|\gamma|<1\) 且 \(\{|x_n|:n\in\mathbb N\}\) 有上界。则

\[
\lim_{n\to\infty}\gamma^n x_n=0.
\]

# 4 Lean 中的马尔可夫假设

**共同性质。** 无论哪种应用，一阶马尔可夫假设都说：长度为 \(n\) 的对象的概率是 \(n\) 个单步因子的乘积，每个因子在合适的状态空间里只回看有限的一步。本文处处用到两个推论：（i）乘积的对数是各因子对数之和，所以得分是逐步项之和；（ii）乘积可以按长度归纳地构造、求和、取最大或求导，这给出线性时间的递推。模型之间的差别是因子如何归一化（第 10 节）。

## 4.1 作为分解的假设

固定一个句子，即观测序列 \(xo\)，以及有限或可数的标签类型 \(\mathcal Y\)。对标签序列 \(ys:\mathbb N\to\mathcal Y\)，令 \(P_t(ys)\) 表示前 \(t+1\) 个观测与标签的联合概率 \(\mathbb P\bigl(x[{:}t{+}1]=xo[{:}t{+}1]\wedge y[{:}t{+}1]=ys[{:}t{+}1]\bigr)\)。

**定义 4.1（`IsHiddenMarkovSeq`）。** 设 \(P:\mathbb N\to(\mathbb N\to\mathcal Y)\to\mathbb R\)，\(\pi:\mathcal Y\to\mathbb R\)，\(T:\mathcal Y\to\mathcal Y\to\mathbb R\)，\(E:\mathbb N\to\mathcal Y\to\mathbb R\)。`IsHiddenMarkovSeq P π T E` 表示对每个 \(ys\)，

\[
P_0(ys)=E_0(ys_0)\,\pi(ys_0),\qquad
P_{t+1}(ys)=P_t(ys)\cdot T(ys_t,ys_{t+1})\,E_{t+1}(ys_{t+1})\quad(t\in\mathbb N).
\]

在我们采用的读法里，\(\pi(a)=\mathbb P(y_0=a)\)，\(T(a,b)=\mathbb P(y_{i+1}=b\mid y_i=a)\)，\(E_i(b)=\mathbb P(x_i=xo_i\mid y_i=b)\)。概率版本 `IsHiddenMarkovPr π x y xo` 直接用概率记号陈述同样两个等式：\(\mathbb P(x[{:}1]=xo[{:}1]\wedge y[{:}1]=ys[{:}1])=\mathbb P(x_0=xo_0\mid y_0=ys_0)\,\mathbb P(y_0=ys_0)\)，以及

\[
\begin{aligned}
&\mathbb P\bigl(x[{:}t{+}2]=xo[{:}t{+}2]\wedge y[{:}t{+}2]=ys[{:}t{+}2]\bigr)\\
&\quad=\mathbb P\bigl(x[{:}t{+}1]=\dots\wedge y[{:}t{+}1]=\dots\bigr)\,\mathbb P(y_{t+1}\mid y_t)\,\mathbb P(x_{t+1}=xo_{t+1}\mid y_{t+1}).
\end{aligned}
\]

`IsHiddenMarkovFac` 是对抽象前缀族 \(P\) 的同一个分解；定理 `IsHiddenMarkovPr.toFac` 从概率版本过渡到它，`IsHiddenMarkovSeq.prefix`（对 `IsHiddenMarkovFac` 也有）用对 \(t\) 的归纳证明 \(P_t\) 只依赖前 \(t+1\) 个标签。下面的 CRF 引理把这些定义和辅助定理当作假设。

**注 4.2（假设与推导）。** 抽象分解 `IsHiddenMarkovSeq` 在定理 5.1 中是**被假设**的。对概率版本 `IsHiddenMarkovPr`，分解是由条件独立**推出**的：观测只通过当前标签依赖于过去，\(x_{t+1}\perp(x[{:}t{+}1],y[{:}t{+}1])\mid y_{t+1}\)；标签只通过前一个标签依赖于过去，\(y_{t+1}\perp(x[{:}t{+}1],y[{:}t])\mid y_t\)。定理 4.3 证明这两条条件独立蕴含乘积形式，引理 [IsHiddenMarkovPr.of.CondIndep.CondIndep](http://www.lemma.cn/lean/?module=Random.IsHiddenMarkovPr.of.CondIndep.CondIndep) 把一步等式打包为 `IsHiddenMarkovPr`。它们必须读作**条件**独立：相应的边缘独立（例如不以 \(y_{t+1}\) 为条件的 \(x_{t+1}\perp(x[{:}t{+}1],y[{:}t{+}1])\)）推不出分解（取 \(x_0\) 为常数，\(y_0,y_1\) 为独立的公平比特，\(x_1=y_0\oplus y_1\)，再加少量噪声使所有概率为正）。同一个 Lean 文件里还有这一分解的决策过程版本（声明 [crf.markov.mdp](http://www.lemma.cn/lean/?module=Random.ProbJoint.eq.Mul_Prod_MulProbSCond.of.All_CondIndep.All_CondIndep.EqMeasure_Count.EqMeasure_Count.All_Measurable.All_Measurable#mdp)）。设 \(s_i\) 为状态、\(a_i\) 为动作（值域可数，参考测度为计数测度），并假设两条条件独立 \(a_t\perp(s[{:}t],a[{:}t])\mid s_t\) 与 \(s_{t+1}\perp(s[{:}t],a[{:}t])\mid(s_t,a_t)\)。那么 \(\mathbb P(s[{:}t{+}1]=\bar s[{:}t{+}1]\wedge a[{:}t]=\bar a[{:}t])\) 等于 \(\mathbb P(s_0=\bar s_0)\) 与各因子 \(\mathbb P(a_i=\bar a_i\mid s_i=\bar s_i)\,\mathbb P(s_{i+1}=\bar s_{i+1}\mid s_i=\bar s_i\wedge a_i=\bar a_i)\) 的乘积。两者的角色对应为（标签，观测）\(\leftrightarrow\)（状态，动作）：都是由两条条件独立经对 \(t\) 归纳得到的一步条件概率之积。有两点差别需要记住。第一，这条 Lean 陈述只针对状态与动作：Python 版本还带有奖励，但这里 \(\mathbb R^t\) 上没有参考测度，并且其边缘独立假设对该分解过弱（与上面的 HMM 情形一样），所以 Lean 版本使用条件独立。第二，对第 6.1 节的 MDP，马尔可夫性不是被假设的，而是由轨迹律的构造（`joint_succ`、`hist_step`）得出；`mdp` 则是对满足这些独立性的一般概率空间上的任意律所作的对应陈述。

## 4.2 乘积形式

**定理 4.3（[crf.markov](http://www.lemma.cn/lean/?module=Random.ProbJoint.eq.Mul_Prod_MulProbSCond.of.All_CondIndep.All_CondIndep.EqMeasure_Count.EqMeasure_Count.All_Measurable.All_Measurable)）。** 设 \(x_i,y_i\) 是标准 Borel 样本空间的概率空间上的可测离散随机变量（值域可数，参考测度为计数测度），且对每个 \(t\)

\[
x_{t+1}\perp\bigl(x[{:}t{+}1],\,y[{:}t{+}1]\bigr)\mid y_{t+1},
\qquad
y_{t+1}\perp\bigl(x[{:}t{+}1],\,y[{:}t]\bigr)\mid y_t .
\]

则对每个 \(xo\)、\(ys\) 与 \(t\)，

\[
\begin{aligned}
&\mathbb P\bigl(x[{:}t{+}1]=xo[{:}t{+}1]\wedge y[{:}t{+}1]=ys[{:}t{+}1]\bigr)\\
&\quad=\mathbb P(x_0=xo_0\mid y_0=ys_0)\,\mathbb P(y_0=ys_0)\prod_{i=1}^{t}\mathbb P(y_i=ys_i\mid y_{i-1}=ys_{i-1})\,\mathbb P(x_i=xo_i\mid y_i=ys_i).
\end{aligned}
\]

证明是对 \(t\) 的归纳，用 `Finset.prod_Ico_succ_top`。一步等式是链式法则 \(\mathbb P(C\cap F\cap E)=\mathbb P(C)\,\frac{\mathbb P(F\cap G)}{\mathbb P(G)}\,\frac{\mathbb P(E\cap F)}{\mathbb P(F)}\)，其中过去事件 \(C=\{x[{:}t{+}1]=xo[{:}t{+}1],\,y[{:}t{+}1]=ys[{:}t{+}1]\}\)，\(E=\{x_{t+1}=xo_{t+1}\}\)，\(F=\{y_{t+1}=ys_{t+1}\}\)，\(G=\{y_t=ys_t\}\supseteq C\)；它由两条条件独立消去分母得到。不需要非零假设：若某个条件事件的概率为零，两边都为零（模块名保留了历史上的 `Ne_0`）。

## 4.3 条件独立：标准构件

库里有三条引理，形式化了通常用来陈述马尔可夫假设的条件独立词汇。设 \(x,y,z\) 是概率空间上的可测随机变量。

- [CondIndep.of.Indep_Joint](http://www.lemma.cn/lean/?module=Random.CondIndep.of.Indep_Joint)：若 \(x\perp(y,z)\)，则 \(x\perp y\mid z\)。
- [Indep_Joint.of.CondIndep.Indep](http://www.lemma.cn/lean/?module=Random.Indep_Joint.of.CondIndep.Indep)：若 \(z\perp x\mid y\) 且 \(z\perp y\)，则 \(z\perp(x,y)\)。
- [All_Imp_EqProbSCond.of.CondIndep](http://www.lemma.cn/lean/?module=Random.All_Imp_EqProbSCond.of.CondIndep)：若 \(x\perp y\mid z\)，则在参考测度几乎处处，只要 \(\mathbb P(y,z)\ne0\)，就有 \(\mathbb P(x\mid y,z)=\mathbb P(x\mid z)\)；这就是条件形式的马尔可夫性。

把联合概率逐个变量分解的链式法则，是离散引理 [ProbCond.eq.Mul.ProbCond](http://www.lemma.cn/lean/?module=Random.ProbCond.eq.Mul.ProbCond)：对值域可数、参考测度为计数测度的变量，\(\mathbb P(x\wedge y\mid z)=\mathbb P(x\mid z)\,\mathbb P(y\mid x\wedge z)\)。它是两变量、逐点的；隐马尔可夫序列的 \(n\) 步链式法则就是定理 4.3，它化归为条件独立的测度形式 [MulMeasure.eq.MulMeasure.of.CondIndep](http://www.lemma.cn/lean/?module=Random.MulMeasure.eq.MulMeasure.of.CondIndep)，\(\mathbb P(x{=}u,y{=}v,z{=}w)\,\mathbb P(z{=}w)=\mathbb P(x{=}u,z{=}w)\,\mathbb P(y{=}v,z{=}w)\)（由上面第三条引理得到，无需非零假设），以及把 \(\mathbb P(x\mid y)\) 等同于测度之比的 [ProbCond.eq.Div.of.Eq_Count.Eq_Count](http://www.lemma.cn/lean/?module=Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count)。

# 5 线性链 CRF 的前向与后向传播

这是第一个核心主题。线性链 CRF 给标签序列 \(ys\in\mathcal Y^{m+1}\) 一个权重，它是单步因子的乘积，配分函数 \(Z\) 是这些权重在全部 \(k^{m+1}\) 个标签序列上的和。马尔可夫结构使两个和能在线性时间内算出：对前缀的**前向**递推（第 5.2 节）与对后缀的**后向**递推（第 5.3 节）；同一条链上把 \(\sum\) 换成 \(\max\) 的第三个递推就是 Viterbi（第 5.4 节）。第 5.2 节与第 5.4 节针对隐马尔可夫条件特例在对数域陈述；第 5.3 节是关于任意实权重的纯代数陈述，隐马尔可夫分解是它的一个实例。

## 5.1 从乘积到得分

记 \(G(a,b)=\log\mathbb P(y_{i+1}=a\mid y_i=b)\) 为从 \(b\) 到 \(a\) 的转移得分，\(e_t(a)=\log\mathbb P(x_t=xo_t\mid y_t=a)\) 为发射（一元）得分，\(s_t(ys)=\log P_t(ys)\) 为标签前缀的对数得分。下面的陈述中所有概率都假设严格为正。

**定理 5.1（[crf.markov.logits](http://www.lemma.cn/lean/?module=Tensor.Eq.of.Ne_0.Eq.Eq.Eq.Eq_log.Eq_log.Eq_log)）。** 设 `IsHiddenMarkovSeq P π T E` 且 \(P,T,E>0\)，\(s_t=\log P_t\)，\(x_t=\log E_t\)，\(G(a,b)=\log T(b,a)\)。则对每个 \(t>0\)，

\[
s_t(ys)=G(ys_t,ys_{t-1})+s_{t-1}(ys)+x_t(ys_t).
\]

**定理 5.2（[crf.logits](http://www.lemma.cn/lean/?module=Tensor.Imp.of.Eq)）。** 设 `IsHiddenMarkovPr π x y xo`，\(\mathbb P(y_0=a)\)、\(\mathbb P(y_{i+1}=a\mid y_i=b)\)、\(\mathbb P(x_t=xo_t\mid y_t=a)\) 为正，且 \(s_t,e_t,G\) 如上。则对每个 \(ys\)，

\[
\begin{aligned}
s_{t+1}(ys)&=G(ys_{t+1},ys_t)+s_t(ys)+e_{t+1}(ys_{t+1}),\\
s_t(ys)&=\log\mathbb P(y_0=ys_0)+\sum_{i=1}^{t}G(ys_i,ys_{i-1})+\sum_{i=0}^{t}e_i(ys_i).
\end{aligned}
\]

第二行就是教科书上线性链 CRF 的得分：一元（发射）项与二元（转移）项之和。它恰是第 4 节的**马尔可夫乘积的对数是逐步项之和**这一性质；神经 CRF [8][11][14] 把 \(e_t\) 换成网络输出、把 \(G\) 当作自由矩阵，苏剑林的推导 [27][27] 也从同一个加性形式出发。

## 5.2 前向传播：log-sum-exp 与前向递推

库里有 softmax 的两个逐点事实：[Log.Softmax.eq.Add.LogSumExp](http://www.lemma.cn/lean/?module=Tensor.Log.Softmax.eq.Add.LogSumExp)，\(\log\frac{e^{x_i}}{\sum_je^{x_j}}=x_i-\log\sum_je^{x_j}\)，以及 [Le_LogSumExp](http://www.lemma.cn/lean/?module=Tensor.Le_LogSumExp)，\(x_i\le\log\sum_je^{x_j}\)；它的雅可比是 [Grad.Softmax.eq.Mul.Softmax](http://www.lemma.cn/lean/?module=Real.Grad.Softmax.eq.Mul.Softmax)：记 \(\sigma_j=e^{F_j}/\sum_ie^{F_i}\)，则 \(\partial\sigma_j=\sigma_j\bigl(\partial F_j-\sum_i\sigma_i\,\partial F_i\bigr)\)。

对前向递推，设 \(\mathcal Y\) 有限、含 \(k\) 个元素，固定长度 \(m+1\)，令

\[
z_t(a)=\sum_{ys\in\mathcal Y^{t+1},\;ys_t=a}e^{s_t(ys)},\qquad \alpha_t(a)=\log z_t(a).
\]

于是 \(z_t(a)\) 是对 \(k^{t}\) 条标签前缀的暴力求和，\(Z=\sum_bz_m(b)\) 是对全部 \(k^{m+1}\) 条标签路径的和。

**定理 5.3（[y_given_x](http://www.lemma.cn/lean/?module=Tensor.Imp_Eq_Add_LogSumExp.EqNegLogProb.of.Ne0ProbJoint.Indep.y_given_x)）。** 在定理 5.2 的假设下（前缀概率为正），

\[
\alpha_{t+1}(a)=\log\sum_{b\in\mathcal Y}\exp\bigl(\alpha_t(b)+G(a,b)\bigr)+e_{t+1}(a),
\]

并且对每个标签序列 \(ys\)，

\[
-\log\mathbb P\bigl(y[{:}m{+}1]=ys[{:}m{+}1]\bigm|x[{:}m{+}1]=xo[{:}m{+}1]\bigr)\;=\;\log\sum_{b\in\mathcal Y}e^{\alpha_m(b)}\;-\;s_m(ys).
\]

由于 \(\sum_be^{\alpha_m(b)}=Z\) 是定义，第二行就是 CRF 的负对数似然 \(-\log p(y\mid x)=\log Z(x)-\text{score}(x,y)\)，第一行是前向递推，它用 \(O(mk^2)\) 时间而不是 \(k^{m+1}\) 项算出 \(Z\)：Lean 对 \(t\) 归纳检验递推与 \(z_t\) 的暴力定义一致（按最后一个标签拆分对 \(\mathcal Y^{t+1}\) 的和，`Fintype.sum_snoc`）。这是借助马尔可夫假设递归地计算归一化因子的递推，也是 Sutton 与 McCallum [28] 所讲的线性链 CRF 的前向算法。在概率域，取 \(P_t=e^{s_t}\)，它写成 \(z_{t+1}(a)=\bigl(\sum_bz_t(b)\,\mathbb P(y_{t+1}=a\mid y_t=b)\bigr)\mathbb P(x_{t+1}=xo_{t+1}\mid y_{t+1}=a)\)；定理 5.4 对任意权重证明的正是这一形式，并连同它的后向对应物。

## 5.3 后向传播与前向--后向恒等式

前向变量 \(z_t(a)\) 概括以标签 \(a\) 结尾的前缀 \(ys_0,\dots,ys_t\)。**后向**变量 \(\beta_t(a)\) 概括时刻 \(t\) 的标签 \(a\) 之后可能接续的后缀 \(ys_{t+1},\dots,ys_m\)。它们的乘积是经过时刻 \(t\) 的标签 \(a\) 的全部标签序列的总权重，所以在隐马尔可夫读法下 \(z_t(a)\beta_t(a)/Z\) 是后验边缘分布 \(\mathbb P(y_t=a\mid x)\)。我们对任意实权重陈述 Lean 定理，因为两个递推既不需要正性也不需要归一化。

**设定。** 设 \(\mathcal Y\) 是有限类型，\(\psi_0:\mathcal Y\to\mathbb R\) 与 \(\psi_t:\mathcal Y\to\mathcal Y\to\mathbb R\)（\(t\ge1\)）是任意实函数，\(P_t:(\mathbb N\to\mathcal Y)\to\mathbb R\) 是前缀权重，满足

\[
P_0(ys)=\psi_0(ys_0),\qquad P_{t+1}(ys)=P_t(ys)\,\psi_{t+1}(ys_t,ys_{t+1})\quad(t\in\mathbb N).\tag{1}
\]

定义 4.1 的隐马尔可夫分解是实例 \(\psi_0(a)=E_0(a)\pi(a)\)、\(\psi_t(a,b)=T(a,b)E_t(b)\)（`IsHiddenMarkovFac` 是带时间相关转移概率的实例）：下面定理的两个假设恰是这些定义的两个字段，所以实例化就是投影 `(h ys).1` 与 `(h ys).2 t`。带自由正势函数 \(\psi_t(y_{t-1},y_t,x)\)（固定输入 \(x\)）的同一个等式 (1) 就是线性链 CRF 的未归一化权重；该定理并不把归一化分布 \(\prod_t\psi_t/Z\) 定义为模型。令

\[
z_t(a)=\sum_{ys\in\mathcal Y^{t+1},\;ys_t=a}P_t(ys)\qquad(\text{当 }P_t=e^{s_t}\text{ 时，这就是第 5.2 节的 }z_t),
\]

固定长度 \(m+1\)，并令后向变量满足

\[
\beta_m(a)=1,\qquad \beta_t(a)=\sum_{c\in\mathcal Y}\psi_{t+1}(a,c)\,\beta_{t+1}(c)\quad(t<m).
\]

**定理 5.4（[crf.forward_backward](http://www.lemma.cn/lean/?module=Tensor.And.of.All_Eq_Sum_Mul.All_Eq_1.All_Eq_Mul.All_Eq.forward_backward)）。** 在上述设定下，对每个 \(a\in\mathcal Y\)：

- （a）（前向递推）\(z_0(a)=\psi_0(a)\)，且对每个 \(t\)，\(z_{t+1}(a)=\sum_{b\in\mathcal Y}z_t(b)\,\psi_{t+1}(b,a)\)；
- （b）（前向--后向恒等式）对每个 \(t\le m\)，\(\sum_{ys\in\mathcal Y^{m+1},\;ys_t=a}P_m(ys)=z_t(a)\,\beta_t(a)\)；
- （c）（配分函数与切分点无关）对每个 \(t\le m\)，\(\sum_{a\in\mathcal Y}z_t(a)\,\beta_t(a)=\sum_{a\in\mathcal Y}z_m(a)=Z\)。

这里 \(Z=\sum_{ys\in\mathcal Y^{m+1}}P_m(ys)\) 是配分函数；(c) 在文件里写成 \(\sum_az_m(a)\)，按 \(z_m\) 的定义（把路径按最后一个标签分组）它等于 \(Z\)，在隐马尔可夫实例里就是定理 5.3 的 \(Z\)。形式化陈述没有正性假设，也没有概率空间；标签序列是函数 \(\mathrm{Fin}(m+1)\to\mathcal Y\)，与其他 CRF 引理一样补成 \(\mathbb N\) 上的函数，\(\beta\) 是满足上面两个后向方程的任意函数。

**证明思路。** (a) 是把对 \(\mathcal Y^{t+2}\) 的和按最后一个标签拆分（`Fintype.sum_snoc`，与定理 5.3 相同），再加上 \(P_t\) 只依赖前 \(t+1\) 个标签这一事实，后者由 (1) 对 \(t\) 归纳证明。对 (b)，固定 \(t\) 与 \(a\)，令 \(u_j(c)\) 为 \(P_j(ys)\) 在 \(ys\in\mathcal Y^{j+1}\)、\(ys_t=a\)、\(ys_j=c\)（\(j\ge t\)）上的和。同样的拆分给出 \(u_{j+1}(c)=\sum_bu_j(b)\psi_{j+1}(b,c)\)，并且当 \(c=a\) 时 \(u_t(c)=z_t(a)\)，否则为 \(0\)。对 \(t\) 向下归纳证明：对满足该递推的任意初始向量 \(u_t\)，\(\sum_cu_m(c)=\sum_au_t(a)\beta_t(a)\)；归纳步交换两个有限和并用后向方程。(c) 是对 \(u=z\) 用同一个归纳，并用 \(\beta_m=1\)。全部是有限和的操作；递推的代价是 \(O(mk^2)\)，\(k=\lvert\mathcal Y\rvert\)。

**读法。** 在隐马尔可夫读法下，\(P_m(ys)=\mathbb P(x[{:}m{+}1]=xo[{:}m{+}1]\wedge y[{:}m{+}1]=ys[{:}m{+}1])\)，\(Z=\mathbb P(x=xo)\)，所以 (b) 说 \(z_t(a)\beta_t(a)\) 等于 \(\mathbb P(x=xo,\,y_t=a)\)，除以 \(Z\) 得到后验边缘 \(\mathbb P(y_t=a\mid x=xo)\)。这一步除法就是定理 5.3 的证明对整条路径已经做过的 Bayes 步；归一化的边缘分布**不是**单独的 Lean 陈述。(c) 是检查每个切分点 \(t\) 给出同一个 \(Z\)：它使前向--后向成为一个一致的分解，而不是两个互不相干的递推。Rabiner [21] 与 Sutton 和 McCallum [28] 给出了教科书形式的前向与后向递推。后向递推的对数域版本是对 \(\log\beta\) 用 \(\log\sum\exp\) 写出的同一个陈述，没有单独形式化。

## 5.4 Viterbi：max-plus 递推

把和换成最大值、把对数换成恒等映射，得到第二个递推。令 \(v_t(a)=\max_{ys\in\mathcal Y^{t+1},\,ys_t=a}s_t(ys)\)。

**定理 5.5（[crf.viterbi](http://www.lemma.cn/lean/?module=Tensor.And.of.Ne_0.Eq.Eq.Eq)）。** 在同样的假设下，

\[
\begin{aligned}
v_{t+1}(a)&=e_{t+1}(a)+\max_{b\in\mathcal Y}\bigl(v_t(b)+G(a,b)\bigr),\\
\max_{ys\in\mathcal Y^{m+1}}\mathbb P\bigl(x[{:}m{+}1]=xo[{:}m{+}1]&\wedge y[{:}m{+}1]=ys\bigr)=\exp\max_{b\in\mathcal Y}v_m(b).
\end{aligned}
\]

只算出了最大**值**；没有 argmax 也没有回溯指针，所以解码出的序列本身没有形式化。定理 5.3 与 5.5 的前向递推是同一条链上同一个递推的两个实例，分别在对数半环（\(\oplus=\) log-sum-exp，\(\otimes=+\)）与 max-plus 半环（\(\oplus=\max\)，\(\otimes=+\)）上；在 Lean 里它们是分别证明的，半环的统一只是一句说明，不是定理。（量 \(v_t\) 与第 5.3 节的后向变量 \(\beta_t\) 无关。）苏剑林 [27] 读出了同样的两个递推，分别用于训练与预测。

## 5.5 HMM 对 CRF：陈述说了什么、没说什么

**HMM。** 隐马尔可夫模型 [21] 是**生成式**、**局部归一化**的：

\[
p(x,y)=\prod_{t}p(y_t\mid y_{t-1})\,p(x_t\mid y_t),\qquad Z=1,
\]

每个因子在自己的变量上都是概率分布。

**线性链 CRF。** 线性链 CRF [10][28] 是**判别式**、**全局归一化**的：

\[
p(y\mid x)=\frac1{Z(x)}\prod_{t}\psi_t(y_{t-1},y_t,x),\qquad Z(x)=\sum_{y'\in\mathcal Y^{n}}\prod_t\psi_t(y'_{t-1},y'_t,x),
\]

势函数 \(\psi_t\) 是任意非负函数，不必是概率；配分函数 \(Z(x)\) 只有一个，是对 \(k^n\) 条标签路径的和。马尔可夫假设使 \(Z(x)\) 能用定理 5.3 的前向递推计算，或等价地用定理 5.4 的前向--后向对计算。就定理 5.2 的得分递推而言，CRF 就是去掉了局部归一化约束的 HMM 得分递推：势函数 \(\psi_t=e^{G+e_t}\) 是自由的，剩下的概率是 \(e^{\text{score}}/Z(x)\)。

**Lean 覆盖了什么。** 定理 5.2、5.3 与 5.5 是 HMM-**条件**特例：\(\psi_t(y_{t-1},y_t,x)=\mathbb P(y_t\mid y_{t-1})\mathbb P(x_t=xo_t\mid y_t)\)，概率为正，此时 \(Z(x)\) 就是证据 \(\mathbb P(x=xo)\)。定理 5.4 对任意实权重 \(\psi_t\) 覆盖前向与后向递推，因而覆盖固定输入下一般势函数 CRF 的代数；但一般势函数的 CRF（任意 \(\psi_t\)、不是条件分布的可训练转移矩阵，因而是真正全局的 \(Z\)）**没有**被定义为模型，需要该模型的量也没有形式化。因此 Lean 的结论 \(-\log p=\log Z-\text{score}\) 是在能由分解假设证出的情形下把 CRF 损失说精确，而不是关于一般 CRF 的证明。

# 6 Bellman 方程

这是第二个核心主题。CRF 引理固定一个已观测的句子并对标签求和；这里随机的是整条轨迹，马尔可夫结构是决策过程的：下一个状态与奖励对过去的依赖只通过当前状态与动作。Bellman 方程说，一个状态的价值是即时奖励的期望加上下一状态折扣后的价值，这是一个一步递推，它代替了无穷视野的期望。

## 6.1 模型与轨迹测度

**定义 6.1（模型）。** 设 \(S\)、\(A\) 是带离散 \(\sigma\)-代数的有限类型，\(\Theta\) 是实赋范空间。**策略**是函数 \(\pi:\Theta\to S\to A\to\mathbb R\)，记作 \(\pi_\theta(u\mid x)\)，满足 \(\pi_\theta(u\mid x)\ge0\)、\(\sum_u\pi_\theta(u\mid x)=1\)（局部归一化：每一步 \(Z=1\)）。**环境**由 \(S\) 上的初始概率测度 \(\iota\)、从 \(S\times A\) 到 \(S\) 的马尔可夫核 \(T\)、从 \(S\times A\) 到 \(\mathbb R\) 的马尔可夫核 \(R\)（奖励律，支撑在 \([-R_{\max},R_{\max}]\) 内）组成。

一条轨迹是阶段序列 \(\omega\in(S\times A\times\mathbb R)^{\mathbb N}\)，坐标记为 \({\color{red}s}_t,{\color{red}a}_t,{\color{red}r}_t\)。从状态 \(x\) 出发走一步由核 \(\kappa_\theta(x)=\delta_x\otimes(\pi_\theta(\cdot\mid x)\otimes R)\) 给出，阶段链的核是 \(K_\theta(x,u,\rho)=(\kappa_\theta\circ T)(x,u)\)。轨迹测度 \(\mathbb P_\theta=\mathtt{Kernel.trajMeasure}\;\mu_0\;(K_\theta)_n\) 是 mathlib 提供的 Ionescu-Tulcea 扩张 [9]，其中第 \(n\) 个核只看历史的最后一个阶段。

有限维边缘分布具有马尔可夫乘积的形状 \(\iota(s_0)\prod_t\pi_\theta(a_t\mid s_t)\,T(s_{t+1}\mid s_t,a_t)\,R(\cdot\mid s_t,a_t)\)。仅就状态与动作而言，该乘积公式就是第 4 节讨论的声明 `mdp`，它在一般概率空间上由条件独立证明；它并没有针对 `Kernel.trajMeasure` 实例化。它的对数是逐步项之和，而转移与奖励因子不依赖于 \(\theta\)，所以**轨迹的得分是各个动作得分之和**，\(\sum_t\nabla_\theta\log\pi_\theta(a_t\mid s_t)\)。这是定理 5.2 中 CRF 得分在 MDP 里的对应物；Lean 只通过下面的期望引理 `E_score` 用到它。

**这里马尔可夫性是定理。** 与注 4.2（分解由假设的条件独立推出）相反，\(\mathbb P_\theta\) 的马尔可夫性是由构造证出来的。模型文件含有 `joint_succ`：\((\omega_t,\omega_{t+1})\) 的分布是 \(\omega_t\) 的分布与核 \(K_\theta\) 的复合；以及 `hist_step`：对有界可测的 \(\varphi\)，

\[
\mathbb E\bigl[\varphi(h_n,\omega_{n+1})\bigr]=\int\Bigl(\int\varphi(h,z)\,dK_\theta(\mathrm{last}\,h)(z)\Bigr)\,d\,\mathrm{law}(h_n)(h),
\]

其中 \(h_n=(\omega_0,\dots,\omega_n)\) 是历史，\(\mathrm{last}\,h\) 是它的最后一个阶段；下面还用到它们的迭代版本（`hist_mul`、`hist_iter`）。状态与动作的联合律分解为 \(\mathbb P(s_t=x,a_t=u)=\mathbb P(s_t=x)\,\pi_\theta(u\mid x)\)（[ProbJoint.eq.Mul_Prob_Pr](http://www.lemma.cn/lean/?module=Random.ProbJoint.eq.Mul_Prob_Pr)）。

## 6.2 价值函数与 Bellman 方程

对 \(\gamma\in[0,1)\)，从 \(t\) 起的折扣回报是 \(G_t=\sum_k{}'\,\gamma^k{\color{red}r}_{t+k}\)，\(V_t^\theta(s_t)=\mathbb E_\theta[G_t\mid{\color{red}s}_t]\)，\(Q_t^\theta(s_t,a_t)=\mathbb E_\theta[G_t\mid{\color{red}s}_t,{\color{red}a}_t]\)。目标函数是 \(J(\theta)=\mathbb E_\theta[\sum_t{}'\,\gamma^t{\color{red}r}_t]=\sum_t{}'\,\gamma^t\mathbb E_\theta[{\color{red}r}_t]\)。模型文件证明了：在可达状态上 \(V_t^\theta\) 等于一个与时间无关的闭式，\(|V_t|,|Q_t|\le(1-\gamma)^{-1}R_{\max}\)，并且对可微且梯度一致有界的策略，\(J\) 是 Fréchet 可微的。我们始终假设：(D) \(\gamma\in[0,1)\)；(P1) \(\theta\mapsto\pi_\theta(u\mid x)\) 可微；(P2) \(\sup_{\theta,x,u}\|\nabla_\theta\pi_\theta(u\mid x)\|<\infty\)。对 \(V_t\) 与 \(\nabla V_t\) 的界是推出来的，不是假设。

**定理 6.2（Bellman 方程 [Bellman](http://www.lemma.cn/lean/?module=Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman)）。** 设 (D) 成立，\(V\)、\(Q\) 满足 \(V_t(s_t)=\mathbb E_\theta[G_t\mid{\color{red}s}_t]\)、\(Q_t(s_t,a_t)=\mathbb E_\theta[G_t\mid{\color{red}s}_t,{\color{red}a}_t]\)。则

\[
\begin{aligned}
V_t(s_t)&=\mathbb E_\theta\bigl[Q_t(s_t,{\color{red}a}_t)\bigm|{\color{red}s}_t\bigr],\\
V_t(s_t)&=\mathbb E_\theta\bigl[{\color{red}r}_t+\gamma\,V_{t+1}({\color{magenta}s}_{t+1})\bigm|{\color{red}s}_t\bigr],\\
Q_t(s_t,a_t)&=\mathbb E_\theta\bigl[{\color{red}r}_t+\gamma\,V_{t+1}({\color{magenta}s}_{t+1})\bigm|{\color{red}s}_t,\ {\color{red}a}_t\bigr].
\end{aligned}
\]

在 Lean 文件里，三个恒等式对每个 \(t\) 与每一对 \((x,u)\) 都成立，没有可达性假设：在零概率的条件事件上两边都是 \(0\)（第 3 节）。证明结合了条件期望的塔性质与上一小节轨迹律的马尔可夫性。从 \(t+1\) 到 \(t\) 读，第二个恒等式是价值函数的**后向**递推，方向与定理 5.4 里 \(\beta_t\) 的递推相同；第 6.3 节比较两者，但不声称有定理。这个递推的梯度是策略梯度定理的第一步（定理 7.1）。

## 6.3 前向、后向与 Bellman 递推并排（类比）

本小节是类比，不是定理：没有任何 Lean 陈述把 CRF 递推与 Bellman 递推联系起来。表 1 列出本文的四个一步递推、各自在马尔可夫链上做的聚合、运行方向，以及证明它的 Lean 陈述。

| 递推 | 一步 | 方向 | 聚合 | Lean |
|---|---|---|---|---|
| CRF 前向 | \(z_{t+1}(a)=\sum_bz_t(b)\,\psi_{t+1}(b,a)\) | 沿 \(t\) 向前 | 对前缀求和（sum-product） | 定理 5.4(a)；对数形式见定理 5.3 |
| CRF 后向 | \(\beta_t(a)=\sum_c\psi_{t+1}(a,c)\,\beta_{t+1}(c)\) | 沿 \(t\) 向后 | 对后缀求和（sum-product） | 定理 5.4(b)、(c) |
| Viterbi | \(v_{t+1}(a)=e_{t+1}(a)+\max_b\bigl(v_t(b)+G(a,b)\bigr)\) | 沿 \(t\) 向前 | 对前缀取最大（max-sum） | 定理 5.5（只有数值） |
| Bellman | \(V_t(s_t)=\mathbb E_\theta[{\color{red}r}_t+\gamma V_{t+1}({\color{magenta}s}_{t+1})\mid{\color{red}s}_t]\) | 沿 \(t\) 向后 | 对下一状态与奖励取期望 | 定理 6.2 |

表 1：马尔可夫链上的一步递推。前三个是对标签路径的动态规划；Bellman 递推是对轨迹的动态规划。

形式上，若在 Bellman 递推里去掉奖励并给定终端价值，它就变成 \(V_t(s)=\sum_cK(s,c)\,V_{t+1}(c)\)，其中 \(K\) 是状态链的一步核，形状恰与后向递推 \(\beta_t(a)=\sum_c\psi_{t+1}(a,c)\beta_{t+1}(c)\) 相同，对应 \(\psi\leftrightarrow K\)、\(\beta_m\leftrightarrow V_m\)。差别是真实的：\(K\) 是概率核（\(\sum_cK(s,c)=1\)），而 \(\psi\) 是未归一化的权重；Bellman 递推带有奖励源项与折扣；Lean 里的价值函数是无穷视野的条件期望，不是有限后缀和。这些递推共有的是机制：马尔可夫结构把全局求和换成一步递推，当量由过去构成时向前，由未来构成时向后。

# 7 策略梯度定理：REINFORCE 与 GAE

这是第三个核心主题。策略梯度定理把折扣回报期望的梯度表示成回报乘以实际所取动作的得分 \(\nabla\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\) 的期望。Lean 由 Bellman 递推出发对时间跨度归纳来证明它，有三种形式：带显式余项的截断形式（定理 7.2）、动作价值形式，以及 REINFORCE 形式（定理 7.3）。由于局部归一化使得分零均值（引理 7.4），回报可以换成优势，这给出无偏优势估计与 GAE（第 7.3 节）。

## 7.1 归纳法证明策略梯度定理

**定理 7.1（递推 [policy_gradient.recursion](http://www.lemma.cn/lean/?module=Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.recursion)，展开 [policy_gradient.induct](http://www.lemma.cn/lean/?module=Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.induct)）。** 设 (D)、(P1)、(P2) 成立，\(s_0\) 可达。则在可达的 \(s_t\) 上 \(\nabla V_t(s_t)=\sum_uQ_t(s_t,u)\nabla\pi_\theta(u\mid s_t)+\gamma\sum_y\mathbb P_\theta({\color{red}s}_{t+1}=y\mid{\color{red}s}_t)\nabla V_{t+1}(y)\)，并且对每个 \(n\)，

\[
\nabla_\theta V_0(s_0)=\sum_{t<n}\gamma^t\sum_y\mathbb P_\theta({\color{red}s}_t=y\mid{\color{red}s}_0)\sum_uQ_t(y,u)\nabla_\theta\pi_\theta(u\mid y)+\gamma^n\sum_y\mathbb P_\theta({\color{red}s}_n=y\mid{\color{red}s}_0)\nabla_\theta V_n(y).
\]

第二个恒等式对 \(n\) 归纳证明：用第一个展开余项，再用 Chapman–Kolmogorov 恒等式合并二重和。

**定理 7.2（截断策略梯度 [policy_gradient](http://www.lemma.cn/lean/?module=Tensor.Eq.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient)）。** 设 (D)、(P1)、(P2) 成立。则对每个 \(n\in\mathbb N\)，

\[
\sum_t{}'\,\gamma^t\nabla_\theta\mathbb E_\theta[{\color{red}r}_t]=\mathbb E_\theta\Bigl[\sum_{t<n}\gamma^tQ_t({\color{magenta}s}_t,{\color{magenta}a}_t)\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\Bigr]+\gamma^n\,\mathbb E_\theta\bigl[\nabla_\theta V_n({\color{magenta}s}_n)\bigr].
\]

证明用引理 `E_score`：\(\mathbb E_\theta[g({\color{red}s}_t,{\color{red}a}_t)\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)]=\sum_y\mathbb P_\theta({\color{red}s}_t=y)\sum_ug(y,u)\nabla_\theta\pi_\theta(u\mid y)\)，即对数导数技巧 \(\pi\nabla\log\pi=\nabla\pi\) 对 \(({\color{red}s}_t,{\color{red}a}_t)\) 的分布求和。虽然是有限和，该定理讨论的仍是折扣无穷视野目标：它对每个截断层级都精确成立，带显式余项。令 \(n\to\infty\)，余项由引理 3.1 和对 \(\nabla V_n\) 在可达状态上的界趋于 \(0\)，得到动作价值形式 [IsFinite.Q_Function](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.IsFinite.Q_Function)：\(\sum_t{}'\,\gamma^t\nabla_\theta\mathbb E_\theta[{\color{red}r}_t]=\sum_t{}'\,\gamma^t\mathbb E_\theta[Q_t({\color{magenta}s}_t,{\color{magenta}a}_t)\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)]\)；再用塔性质 [Q_Function.discounted](http://www.lemma.cn/lean/?module=Tensor.Eq.Expect.Grad.Log.Pr.of.Eq_Conditioned.Q_Function.discounted)，\(\mathbb E_\theta[G_t\nabla_\theta\log\pi_\theta]=\mathbb E_\theta[Q_t\nabla_\theta\log\pi_\theta]\)，得到 REINFORCE 形式。

**定理 7.3（策略梯度，REINFORCE 形式 [policy_gradient_theorem](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.IsFinite.policy_gradient_theorem)）。** 设 \(\Theta\) 是实 Hilbert 空间，\(S\)、\(A\) 以计数测度为参考测度，(D)、(P1)、(P2) 成立。则

\[
\nabla_\theta\mathbb E_\theta\Bigl[\sum_t{}'\,\gamma^t{\color{red}r}_t\Bigr]=\mathbb E_\theta\Bigl[\sum_t{}'\,\gamma^t\,G_t\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\Bigr].
\]

这里级数在期望之内；这是因为奖励有界，共用引理 [Log.Pr.of.Bounded](http://www.lemma.cn/lean/?module=Tensor.Eq.Expect.Sum.Grad.Log.Pr.of.Bounded) 与 [Log.Pr.of.Bounded.Discount](http://www.lemma.cn/lean/?module=Tensor.Eq.Expect.Sum.Grad.Log.Pr.of.Bounded.Discount) 完成级数与期望的交换。

## 7.2 归一化给出零均值得分

把定义 6.1 的局部归一化与方差缩减联系起来的性质如下。

**引理 7.4（[Expect_ConditionedGrad_LogProb.eq.Zero](http://www.lemma.cn/lean/?module=Random.Expect_ConditionedGrad_LogProb.eq.Zero)）。** 设 \(p:\Theta\to A\to\mathbb R\)，对所有 \(\theta'\) 有 \(\sum_ap_{\theta'}(a)=1\)，\(p_\theta(a)>0\)，且 \(\theta'\mapsto p_{\theta'}(a)\) 在 \(\theta\) 可微。则 \(\mathbb E_{a\sim p_\theta}[\nabla_\theta\log p_\theta(a)]=\sum_ap_\theta(a)\nabla_\theta\log p_\theta(a)=0\)。

证明只有一行：\(p\nabla\log p=\nabla p\)，而 \(\nabla\sum_ap=\nabla1=0\)。对轨迹模型里的策略，它的条件形式是 [LogProb.eq.Zero.policy](http://www.lemma.cn/lean/?module=Random.Expect_ConditionedGrad_LogProb.eq.Zero.policy)：对正的可微策略，\(\mathbb E_\theta[\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\mid{\color{red}s}_t=x]=0\)。模型文件里同一事实不需要正性也成立（\(\pi_\theta(u\mid x)=0\) 的项为零）：对每个 \(h:S\to\mathbb R\)，\(\mathbb E_\theta[h({\color{red}s}_t)\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)]=0\)（`E_h_score`）。这就是只依赖状态的基线不改变策略梯度的原因，第 7.3 节用的就是这一步。对全局归一化的 CRF，对应的事实不同：\(\mathbb E_{p(y\mid x)}[\nabla\log p(y\mid x)]=0\) 同样成立，但 \(\nabla\log p=\nabla\text{score}-\mathbb E[\nabla\text{score}]\) 含有配分函数；恒等式 \(\nabla\log Z=\mathbb E[\nabla\text{score}]\) 没有形式化。

## 7.3 无偏优势估计与广义优势估计

记 \(\delta_j={\color{red}r}_j+\gamma V_{j+1}({\color{red}s}_{j+1})-V_j({\color{red}s}_j)\) 为价值函数 \(V\) 的时序差分残差。

**定理 7.5（无偏优势估计 [unbiased_advantage_estimate](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.unbiased_advantage_estimate)）。** 设 \(\Theta\) 是实 Hilbert 空间，\(S\)、\(A\) 以计数测度为参考测度，(D)、(P1)、(P2) 成立，且对所有 \(\theta,t\) 和所有可达 \(s_t\) 有 \(V^\theta_t(s_t)=\mathbb E_\theta[G_t\mid{\color{red}s}_t]\)。令 \(\hat A_t=\sum_k{}'\,\gamma^k\delta_{t+k}\)，则

\[
\nabla_\theta\mathbb E_\theta\Bigl[\sum_t{}'\,\gamma^t{\color{red}r}_t\Bigr]=\mathbb E_\theta\Bigl[\sum_t{}'\,\gamma^t\,\hat A_t\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\Bigr].
\]

对有界的 \(V\)，级数裂项相消为 \(\hat A_t=G_t-V_t({\color{red}s}_t)\)，所以定理 7.5 化归为定理 7.3，加上基线项消失 \(\mathbb E_\theta[V_t({\color{red}s}_t)\nabla_\theta\log\pi_\theta]=0\)（第 7.2 节）。

**定理 7.6（广义优势估计 [generalized_advantage_estimate](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.generalized_advantage_estimate)）。** 在定理 7.5 的假设下，设 \(\lambda\in[0,1]\)，\(\hat A^{\lambda}_t=\sum_k{}'\,(\gamma\lambda)^k\delta_{t+k}\)。则

\[
\nabla_\theta\mathbb E_\theta\Bigl[\sum_t{}'\,\gamma^t{\color{red}r}_t\Bigr]=\mathbb E_\theta\Bigl[\sum_t{}'\,\gamma^t\,\hat A^{\lambda}_t\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\Bigr].
\]

对 \(\lambda\in[0,1)\)，[Schulman 等人](https://arxiv.org/abs/1506.02438) [23] 的加权平均形式 \(\hat A^{\lambda}_t=(1-\lambda)\sum_{k\ge0}\lambda^k\sum_{i\le k}\gamma^i\delta_{t+i}\) 给出同一个恒等式 [In_Ico.generalized_advantage_estimate](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.In_Ico.generalized_advantage_estimate)，经由级数恒等式 [IsFinite.generalized_advantage_estimate](http://www.lemma.cn/lean/?module=Tensor.EqDot.of.IsFinite.generalized_advantage_estimate)。原因是对精确价值函数，\(\mathbb E[\delta_{n+1}\psi({\color{red}s}_t,{\color{red}a}_t)]=0\)（\(t\le n\)；马尔可夫性加 Bellman 方程），所以与得分相乘后只有第一个残差留下。这些陈述针对精确价值函数：用近似的 critic 时，\(k\ge1\) 的项不一定零均值，\(\lambda<1\) 是有偏的 [23]；这一点没有形式化。

# 8 PPO：Lean 覆盖什么、不覆盖什么

**MDP 对 PPO。** MDP 是**模型**，PPO 是建立在它之上的**算法**。第 6、7 节的一切都关于模型：轨迹测度及其马尔可夫性、Bellman 方程、策略梯度定理、优势与 GAE。PPO [25] 加上了：重要性比 \(\rho_t(\theta)=\pi_\theta(a_t\mid s_t)/\pi_{\theta_{\rm old}}(a_t\mid s_t)\)；裁剪替代目标

\[
L^{\rm CLIP}(\theta)=\hat{\mathbb E}_t\bigl[\min\bigl(\rho_t(\theta)\hat A_t,\;\mathrm{clip}(\rho_t(\theta),1-\epsilon,1+\epsilon)\hat A_t\bigr)\bigr];
\]

在同一批轨迹上做多轮小批量随机更新；带价值损失（常常也裁剪）的学习得到的价值网络；熵奖励；以及在 RLHF [32][19] 里对参考策略的逐词元 KL 惩罚。这些都没有形式化。

**定理对 PPO 给出什么。**（i）PPO 的优势估计是截断 GAE（其公式 (10)–(11)）；定理 7.6 对精确价值函数证明了**未截断**的估计在策略梯度里是对得分的无偏权重。（ii）在 \(\theta=\theta_{\rm old}\) 处比值为 \(1\)，且 \(\nabla\rho_t=\nabla\log\pi_\theta(a_t\mid s_t)\)，所以未裁剪替代目标的梯度就是定理 7.6 的被积式；这个一行的微积分说明不是 Lean 陈述。（iii）语言模型的情形是一个 MDP：状态 \((x,y_{<t})\)，动作是下一个词元，转移确定，奖励在最后一个词元；这个实例同样没有形式化（第 9 节）。

**没有覆盖的。** 没有裁剪替代目标和重要性比，没有 TRPO 式的 KL 约束或 KL 惩罚（库里有 \(\mathrm{KL}\ge0\)，[Random.KL.ge.Zero](http://www.lemma.cn/lean/?module=Random.KL.ge.Zero)，它不进入任何 PPO 陈述），没有价值裁剪，没有学习得到的 critic 及其偏差，没有截断视野的 GAE，没有奖励模型，没有小批量采样，也没有单调改进或收敛的结论。Lean 论证的是（截断）GAE 优势估计**在策略梯度之内**的合理性；它不论证裁剪目标。

# 9 超越核心：从标注到生成（概念性）

本节是比较，不是定理，也不属于三个核心主题。库里没有序列到序列、教师强制、exposure bias 或 label bias 的引理；它有的是比较中要组合的两块砖。

**同一个分子的两种归一化。** 设 \(\text{score}(x,y)=\sum_tf_t(y_{<t},y_t;x)\) 是加性得分。**全局归一化**模型令 \(p(y\mid x)=e^{\text{score}(x,y)}/Z(x)\)，\(Z(x)=\sum_{y'}e^{\text{score}(x,y')}\)，故 \(-\log p=\log Z(x)-\text{score}(x,y)\)；对线性链，定理 5.3 精确地算出 \(Z\)。**局部归一化**模型对每一步用自己的 softmax 归一化，\(p(y\mid x)=\prod_tp(y_t\mid x,y_{<t})\)，\(p(y_t\mid\cdot)=e^{f_t}/\sum_ve^{f_t(v)}\)，于是

\[
-\log p(y\mid x)=\sum_t\Bigl(\log\sum_ve^{f_t(v)}-f_t(y_t)\Bigr)=\sum_t\bigl(\log Z_t-f_t(y_t)\bigr).
\]

每个加项正是第 5 节的 Lean 恒等式 [Log.Softmax.eq.Add.LogSumExp](http://www.lemma.cn/lean/?module=Tensor.Log.Softmax.eq.Add.LogSumExp)；乘积变求和这一步，是同一个“马尔可夫乘积的对数是逐步项之和”的性质。两种模型有同一个分子，只差分母：一个 \(Z(x)\) 对一串逐步归一化项的乘积。MEMM [18] 是 CRF 的局部归一化的同类，其 label bias 问题（出边少的状态不管观测如何都把全部质量传下去）对应于序列到序列模型的 exposure bias。Andor 等人 [1] 为全局归一化的神经句法分析器提出了同样的主张。

**从标注到生成，什么变了。**

1. **对齐与观测。** 标注中 \(|y|=|x|\)，每个位置上 \(x\) 都完全可见；生成中输出长度可变，没有对齐，已生成的前缀 \(y_{<t}\) 是第 \(t\) 步条件的一部分。我们把“序列到序列”一词留给不对齐的自回归情形。
2. **马尔可夫结构被搬了家。** 线性链 CRF 对**标签**是一阶的，对 \(x\) 则任意；自回归模型 \(p(y_t\mid x,y_{<t})\) 以**整个前缀**为条件，因此只在扩大的状态 \((x,y_{<t})\) 上才是马尔可夫的。在该状态空间里转移是确定性的（追加所选词元），马尔可夫性是平凡的。
3. **归一化项。** 对 \(k^n\) 条路径的 \(Z(x)\) 因一阶依赖可用动态规划在 \(O(nk^2)\) 内算出；对依赖前缀的模型，对 \(V^n\) 条序列的全局和没有这样的递推，所以改为局部归一化。
4. **推断。** Viterbi 对链是精确的；贪心、beam 与采样对生成是近似的。
5. **训练。** 标注最小化监督的 \(\log Z-\text{score}\)。生成用教师强制的交叉熵训练（需要真实前缀），或用期望奖励训练，策略梯度就是在这里出场的（第 7 节）。

**一个 beam search 的例子。** 考虑一个两步的例子：\(p(a)=0.6\)，\(p(c)=0.4\)，\(p(b\mid a)=0.55\)，\(p(d\mid a)=0.45\)，\(p(b\mid c)=0.1\)，\(p(d\mid c)=0.9\)。贪心解码（beam 大小 1）返回 \((a,b)\)，概率 \(0.33\)；beam 大小 2 返回 \((c,d)\)，概率 \(0.36\)，是四条序列（\(0.33,\,0.27,\,0.04,\,0.36\)）中的全局最大。局部归一化模型被其逐步决策所束缚。这个例子没有在 Lean 中检查。

# 10 对比表

## 10.1 各模型中的马尔可夫假设

表 2 比较各个模型分解的是什么、每个因子以什么为条件、如何归一化、Lean 里有什么。每一行里，长度为 \(n\) 的对象的概率都是单步因子的乘积，由此得到：（i）对数中是局部项之和；（ii）线性时间的递推（前向、后向、Viterbi、Bellman、值迭代）；（iii）以对 \(t\) 归纳作为证明技术（CRF 引理对 \(t\) 归纳；MDP 用 `hist_step` 与展开）。

| 模型 | 分解 | 条件于 | 归一化 | Lean |
|---|---|---|---|---|
| HMM | \(p(x,y)=\prod_tp(y_t\mid y_{t-1})\,p(x_t\mid y_t)\)（生成式） | 前一个标签；发射只依赖当前标签 | 局部，\(Z=1\) | `IsHiddenMarkovSeq`/`Pr`，`crf.markov`（由条件独立推出） |
| 线性链 CRF | \(p(y\mid x)=\frac1{Z(x)}\prod_t\psi_t(y_{t-1},y_t,x)\)（判别式） | 相邻标签；\(x\) 任意、完全可见 | 全局 \(Z(x)\)，对 \(k^n\) 条路径 | HMM-条件特例：`crf.logits`、\(\log Z-\)score、`crf.viterbi`；任意权重的前向与后向递推（`crf.forward_backward`）；一般 \(\psi_t\) 作为模型、归一化边缘与 \(\nabla\log Z\) 未形式化 |
| MEMM | \(\prod_tp(y_t\mid y_{t-1},x)\) | 前一个标签与 \(x\) | 局部，逐步 softmax | 未形式化 |
| MDP / 策略梯度 | \(\iota(s_0)\prod_t\pi_\theta(a_t\mid s_t)T(s_{t+1}\mid s_t,a_t)\) | 下一状态与奖励只依赖 \((s_t,a_t)\)；策略只依赖 \(s_t\) | 局部，\(Z=1\) | 轨迹测度、`joint_succ`、`hist_step`、Bellman、策略梯度、优势、GAE |
| PPO（算法） | 同样的轨迹律；目标 \(L^{\rm CLIP}\)，带比值 \(\rho_t\) 与学习得到的 critic | 同 MDP | 局部，\(Z=1\) | **无**：裁剪替代目标、比值、KL、价值裁剪、学习得到的 critic 都未形式化；只有策略梯度之内的（截断）GAE 优势得到论证（精确 \(V\)） |
| 自回归语言模型 | \(\prod_tp(y_t\mid x,y_{<t})\) | 整个前缀 | 局部，逐步 softmax | 未形式化（只有 log-softmax 与两变量链式法则）；作为状态为 \((x,y_{<t})\) 的 MDP，马尔可夫性是平凡的 |

表 2：本文各模型中的马尔可夫假设。HMM 对 CRF 的差别在归一化（局部对全局）以及建模对象（\(p(x,y)\) 对 \(p(y\mid x)\)）；MDP 对 PPO 的差别在种类（模型对算法）。

## 10.2 序列标注对序列到序列生成

表 3 概括第 9 节，是概念性对比；只有标“Lean”的条目是定理，其余都是概念性比较。

| | 序列标注（CRF） | 序列到序列生成（语言模型 / PPO） |
|---|---|---|
| 输入 / 对齐 | 对齐，\(\lvert y\rvert=\lvert x\rvert\)，\(x\) 完全可见 | 不对齐，长度可变；已生成的前缀是条件的一部分 |
| 归一化 | 对 \(k^n\) 条标签序列的全局配分函数 | 局部归一化的词元 softmax |
| 依赖 | 相邻标签（一阶）与整个 \(x\) | 整个前缀 \(y_{<t}\)（以及 \(x\)）；只在状态 \((x,y_{<t})\) 上是马尔可夫的 |
| 训练 | 监督似然，NLL \(=\log Z-\)score（Lean，HMM-条件特例） | 教师强制的交叉熵，或期望奖励（策略梯度 / PPO） |
| 推断 | 精确动态规划：前向、后向、Viterbi（Lean：前向与后向的和；Viterbi 只有数值） | 近似：贪心、beam、采样 |
| 失效模式 | 若局部归一化则 label bias（MEMM）；独立 softmax 会出现非法标签序列 | exposure bias；beam 大小反常（第 9 节的例子） |
| 梯度 | \(\nabla\text{NLL}=\mathbb E_{\rm model}[\text{features}]-\text{empirical}\)（不在 Lean 中） | \(\nabla\mathbb E[R]=\mathbb E[\sum_t\gamma^t\hat A_t\nabla\log\pi_\theta(a_t\mid s_t)]\)（Lean，有限 \(S,A\)，精确 \(V\)）；\(\mathbb E[\nabla\log\pi]=0\)（Lean） |

表 3：序列标注对序列到序列生成。

# 11 形式化工件

**模块与版本。** 每条定理都链接到 [math-proof/lemma](https://github.com/math-proof/lemma) [15] 中对应的模块（省略前缀 `Lemma.`）。本文的陈述对应提交 `5a58c908e` 之后的工作区：撰写时，CRF 引理（第 5 节），包括定理 5.4 的新前向--后向引理、含 `IsHiddenMarkovSeq` 的文件、优势与 GAE 文件及其辅助引理尚未提交。时序差分引理（`delta_ae_bdd`、`E_delta_psi`、`E_sum_delta`）在轨迹模型的优势文件里；取代对 \(V\) 与 \(\nabla V\) 之假设的界 `V_bdd` 与 `gradV_bdd` 在可微性文件里。项目使用 Lean `v4.33.1` 与 mathlib（版本 `0df444a`）。

**检查。** 所引用的模块中都没有 `sorry`、`admit` 或新增 `axiom`。`#print axioms` 对定理 4.3–5.5 的声明、第 4 节至第 7.2 节的 log-softmax、条件独立、链式法则与零得分引理，以及定理 6.2–7.6 和辅助引理，给出的公理都只有 `propext`、`Classical.choice`、`Quot.sound`。

# 12 讨论、局限与结论

**正则性。** 强化学习一侧的定理用到有限的 \(S\) 与 \(A\)（计数测度）、有界奖励、\(\gamma<1\)、可微性以及一致梯度界 (P1)、(P2)。对 \(V_t\) 与 \(\nabla V_t\) 的界由这些推出，不是假设。标注一侧的定理假设概率严格为正，使对数有定义。

**没有形式化的。** 下面列出对本文叙述要紧的缺口。

- **一般 CRF。** 对数域引理只覆盖隐马尔可夫条件特例；带任意正势函数 \(\psi_t(y_{t-1},y_t,x)\) 及其归一化 \(Z(x)\) 的 CRF 没有被定义为模型。马尔可夫结构以分解假设（`IsHiddenMarkovSeq`、`IsHiddenMarkovPr`，或定理 5.4 的链 (1)）的形式进入下游引理；`IsHiddenMarkovPr` 由条件独立推出（定理 4.3），但没有 CRF 的构造推出它。
- **推断。** 前向递推、后向递推与前向--后向恒等式（定理 5.4）以及 Viterbi 的**数值**被覆盖。没有覆盖：归一化的后验边缘与成对边缘、梯度 \(\nabla\log Z=\mathbb E[\nabla\,\text{score}]\)、对数域的后向递推，以及带回溯指针的 argmax Viterbi 路径。
- **生成。** 没有序列到序列模型，没有教师强制引理，没有关于 label bias 或 exposure bias 的陈述，也没有“语言模型即 MDP”的实例。第 9 节是比较，不是定理。
- **类比。** 前向、后向与 Bellman 递推之间的对应（第 6.3 节）不是 Lean 陈述。
- **PPO。** 没有裁剪目标、重要性比、KL 或价值裁剪、学习得到的 critic、截断 GAE、奖励模型、单调改进或收敛（第 8 节）。
- **GAE。** 只对精确价值函数；\(\lambda<1\) 配合近似 critic 带来的偏差没有分析。
- **空间。** \(S\)、\(A\) 有限；连续或词表规模的空间只在它们有限的意义下被覆盖。

**把各部分合起来读。** Lean 确实建立的是共同的机制：马尔可夫乘积变成逐步项之和；链上的递推用来代替对指数多条路径的求和（CRF 的前向与后向、Viterbi、价值函数的 Bellman 递推）；局部因子的归一化使它的得分成为零均值项。选择哪种归一化，决定递推算出的是配分函数（CRF）、已经等于一的概率（HMM、策略），还是最大值（Viterbi）。这些就是从 CRF 走向 PPO 的路上出现的对象。

**结论。** 我们给出了从线性链 CRF 到策略梯度强化学习路径上三个递推的一份 Lean 4 说明。对 CRF，我们形式化了 Markov 乘积、对数得分分解、带负对数似然的前向递推、Viterbi 数值递推，以及对任意权重的前向--后向定理，含后向递推与恒等式 \(\sum_{ys_t=a}P_m(ys)=z_t(a)\beta_t(a)\)。对强化学习，我们形式化了 MDP 轨迹测度、Bellman 方程、截断、动作价值与 REINFORCE 三种形式的策略梯度定理、零均值得分、无偏优势与精确 \(V\) 下的 GAE。我们认真区分了什么是定理、什么是概念性比较。自然的后续是：成对边缘与归一化边缘，以及一般势函数 CRF 的恒等式 \(\nabla\log Z=\mathbb E[\nabla\,\text{score}]\)，带回溯指针的 Viterbi argmax，作为确定性转移 MDP 的局部归一化自回归模型，以及 PPO 替代目标背后的重要性比恒等式。

# 致谢

[mathlib](https://leanprover-community.github.io/mathlib4_docs/) [16][17] 提供了本文每条定理所依赖的测度论与分析。苏剑林在“科学空间”的文章是我们理解 CRF 与 exposure bias 材料的向导 [27][30]。本文引用的各模块的交互式陈述见 [lemma.cn](http://www.lemma.cn/)。

# 参考文献

[1] Daniel Andor, Chris Alberti, David Weiss, Aliaksei Severyn, Alessandro Presta, Kuzman Ganchev, Slav Petrov, Michael Collins. Globally Normalized Transition-Based Neural Networks. ACL, 2016. [arXiv:1603.06042](https://arxiv.org/abs/1603.06042).

[2] Dzmitry Bahdanau, Kyunghyun Cho, Yoshua Bengio. Neural Machine Translation by Jointly Learning to Align and Translate. ICLR, 2015. [arXiv:1409.0473](https://arxiv.org/abs/1409.0473).

[3] Samy Bengio, Oriol Vinyals, Navdeep Jaitly, Noam Shazeer. Scheduled Sampling for Sequence Prediction with Recurrent Neural Networks. NeurIPS 28, 2015. [arXiv:1506.03099](https://arxiv.org/abs/1506.03099).

[4] Mark Chevallier, Jacques Fleuriot. Formalising the Foundations of Discrete Reinforcement Learning in Isabelle/HOL. 2021. [arXiv:2112.05996](https://arxiv.org/abs/2112.05996).

[5] Ronan Collobert, Jason Weston, Léon Bottou, Michael Karlen, Koray Kavukcuoglu, Pavel Kuksa. Natural Language Processing (Almost) from Scratch. *Journal of Machine Learning Research* 12:2493–2537, 2011. [arXiv:1103.0398](https://arxiv.org/abs/1103.0398).

[6] Leonardo de Moura, Sebastian Ullrich. The Lean 4 Theorem Prover and Programming Language. CADE 28, LNCS 12699, pp. 625–635, Springer, 2021.

[7] Evan Greensmith, Peter L. Bartlett, Jonathan Baxter. Variance Reduction Techniques for Gradient Estimates in Reinforcement Learning. *Journal of Machine Learning Research* 5:1471–1530, 2004.

[8] Zhiheng Huang, Wei Xu, Kai Yu. Bidirectional LSTM-CRF Models for Sequence Tagging. 2015. [arXiv:1508.01991](https://arxiv.org/abs/1508.01991).

[9] Olav Kallenberg. *Foundations of Modern Probability*. 2nd ed., Springer, 2002.

[10] John D. Lafferty, Andrew McCallum, Fernando C. N. Pereira. Conditional Random Fields: Probabilistic Models for Segmenting and Labeling Sequence Data. ICML, pp. 282–289, 2001.

[11] Guillaume Lample, Miguel Ballesteros, Sandeep Subramanian, Kazuya Kawakami, Chris Dyer. Neural Architectures for Named Entity Recognition. NAACL-HLT, pp. 260–270, 2016. [arXiv:1603.01360](https://arxiv.org/abs/1603.01360).

[12] Peter J. Landin. The Mechanical Evaluation of Expressions. *The Computer Journal* 6(4):308–320, 1964.

[13] lean-dojo. TorchLean: Formalizing Neural Networks in Lean. GitHub repository, 2026. [lean-dojo/TorchLean](https://github.com/lean-dojo/TorchLean)

[14] Xuezhe Ma, Eduard Hovy. End-to-end Sequence Labeling via Bi-directional LSTM-CNNs-CRF. ACL, pp. 1064–1074, 2016. [arXiv:1603.01354](https://arxiv.org/abs/1603.01354).

[15] math-proof. lemma: machine-checked tensor calculus. 2026. [math-proof/lemma](https://github.com/math-proof/lemma)

[16] Mathlib community. The Lean mathematical library. 2026. [mathlib4_docs](https://leanprover-community.github.io/mathlib4_docs/)

[17] The mathlib Community. The Lean Mathematical Library. CPP, pp. 367–381, ACM, 2020.

[18] Andrew McCallum, Dayne Freitag, Fernando C. N. Pereira. Maximum Entropy Markov Models for Information Extraction and Segmentation. ICML, pp. 591–598, 2000.

[19] Long Ouyang, Jeffrey Wu, Xu Jiang, Diogo Almeida, Carroll L. Wainwright, Pamela Mishkin, Chong Zhang, Sandhini Agarwal, Katarina Slama, Alex Ray, John Schulman, Jacob Hilton, Fraser Kelton, Luke Miller, Maddie Simens, Amanda Askell, Peter Welinder, Paul Christiano, Jan Leike, Ryan Lowe. Training Language Models to Follow Instructions with Human Feedback. NeurIPS 35, 2022. [arXiv:2203.02155](https://arxiv.org/abs/2203.02155).

[20] Martin L. Puterman. *Markov Decision Processes: Discrete Stochastic Dynamic Programming*. Wiley, 1994.

[21] Lawrence R. Rabiner. A Tutorial on Hidden Markov Models and Selected Applications in Speech Recognition. *Proceedings of the IEEE* 77(2):257–286, 1989.

[22] Marc'Aurelio Ranzato, Sumit Chopra, Michael Auli, Wojciech Zaremba. Sequence Level Training with Recurrent Neural Networks. ICLR, 2016. [arXiv:1511.06732](https://arxiv.org/abs/1511.06732).

[23] John Schulman, Philipp Moritz, Sergey Levine, Michael Jordan, Pieter Abbeel. High-Dimensional Continuous Control Using Generalized Advantage Estimation. ICLR, 2016. [arXiv:1506.02438](https://arxiv.org/abs/1506.02438).

[24] John Schulman, Sergey Levine, Philipp Moritz, Michael Jordan, Pieter Abbeel. Trust Region Policy Optimization. ICML, 2015. [arXiv:1502.05477](https://arxiv.org/abs/1502.05477).

[25] John Schulman, Filip Wolski, Prafulla Dhariwal, Alec Radford, Oleg Klimov. Proximal Policy Optimization Algorithms. 2017. [arXiv:1707.06347](https://arxiv.org/abs/1707.06347).

[26] Zhihong Shao, Peiyi Wang, Qihao Zhu, Runxin Xu, Junxiao Song, Xiao Bi, Haowei Zhang, Mingchuan Zhang, Y. K. Li, Y. Wu, Daya Guo. DeepSeekMath: Pushing the Limits of Mathematical Reasoning in Open Language Models. 2024. [arXiv:2402.03300](https://arxiv.org/abs/2402.03300).

[27] 苏剑林. 果壳中的条件随机场(CRF In A Nutshell). 科学空间, 2017. [spaces.ac.cn/archives/4695](https://spaces.ac.cn/archives/4695)

[28] Charles Sutton, Andrew McCallum. An Introduction to Conditional Random Fields. *Foundations and Trends in Machine Learning* 4(4):267–373, 2012. [arXiv:1011.4088](https://arxiv.org/abs/1011.4088).

[29] Jianlin Su, Ahmed Murtadha, Shengfeng Pan, Jing Hou, Jun Sun, Wanwei Huang, Bo Wen, Yunfeng Liu. Global Pointer: Novel Efficient Span-based Approach for Named Entity Recognition. 2022. [arXiv:2208.03054](https://arxiv.org/abs/2208.03054).

[30] 苏剑林. 科学空间：“CRF”搜索结果. 2026. [spaces.ac.cn/search/CRF](https://spaces.ac.cn/search/CRF/)

[31] Ilya Sutskever, Oriol Vinyals, Quoc V. Le. Sequence to Sequence Learning with Neural Networks. NeurIPS 27, 2014. [arXiv:1409.3215](https://arxiv.org/abs/1409.3215).

[32] Daniel M. Ziegler, Nisan Stiennon, Jeffrey Wu, Tom B. Brown, Alec Radford, Dario Amodei, Paul Christiano, Geoffrey Irving. Fine-Tuning Language Models from Human Preferences. 2019. [arXiv:1909.08593](https://arxiv.org/abs/1909.08593).

[33] Richard S. Sutton, David McAllester, Satinder Singh, Yishay Mansour. Policy Gradient Methods for Reinforcement Learning with Function Approximation. NeurIPS 12, pp. 1057–1063, MIT Press, 2000.

[34] Richard S. Sutton, Andrew G. Barto. *Reinforcement Learning: An Introduction*. 2nd ed., MIT Press, 2018.

[35] Koundinya Vajjha, Avraham Shinnar, Barry Trager, Vasily Pestun, Nathan Fulton. CertRL: Formalizing Convergence Proofs for Value and Policy Iteration in Coq. CPP, pp. 18–31, ACM, 2021. arXiv:2009.11403.

[36] Ashish Vaswani, Noam Shazeer, Niki Parmar, Jakob Uszkoreit, Llion Jones, Aidan N. Gomez, Łukasz Kaiser, Illia Polosukhin. Attention Is All You Need. NeurIPS 30, 2017. [arXiv:1706.03762](https://arxiv.org/abs/1706.03762).

[37] Ronald J. Williams. Simple Statistical Gradient-Following Algorithms for Connectionist Reinforcement Learning. *Machine Learning* 8(3–4):229–256, 1992.

[38] Sam Wiseman, Alexander M. Rush. Sequence-to-Sequence Learning as Beam-Search Optimization. EMNLP, 2016. [arXiv:1606.02960](https://arxiv.org/abs/1606.02960).

[39] Shangtong Zhang. rl-theory-in-lean: RLTheory/Algorithm/PolicyGradient.lean, commit 2a9d01a. GitHub, 2026-03-30. [commit 2a9d01a](https://github.com/ShangtongZhang/rl-theory-in-lean/commit/2a9d01a236961b1c9bc451a8926346364fc66e7f)（实验性的、主要由机器生成的开发，其提交与 AI 助手共同署名，后从项目 main 分支撤回，在该提交处仍可访问）
