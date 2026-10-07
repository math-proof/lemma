项目工件：[math-proof/lemma](https://github.com/math-proof/lemma)

CRF 损失函数：[CRF loss function](http://www.lemma.cn/lean/?module=Random.All_Eq_AddLogSumExpAdd.All_EqNegLogProb.of.All_Eq_Log.All_Eq_Sum_Exp.All_Eq_LogProbCond.All_Eq_LogProbCond.All_Eq_LogProbJoint.All_Lt0Prob.IsDiscreteHMM)，Viterbi：[crf.viterbi](http://www.lemma.cn/lean/?module=Random.All_Eq_Add_MaxAdd.EqMax_ProbJoint.of.All_Eq_Max.Eq_LogProbCond.Eq_LogProbCond.Eq_LogProbJoint.All_Lt0ProbJoint.IsDiscreteHMM)，HMM 恒等式：[hmm_identity](http://www.lemma.cn/lean/?module=Random.Sum_Mul_ProbCond.eq.Prob.of.IsDiscreteHMM)

Bellman：[Bellman](http://www.lemma.cn/lean/?module=Random.Eq_Expect.Eq_Expect.Eq_Expect.of.All_Eq_Expect.All_Eq_Expect.In_Ico)，REINFORCE：[Lean 4](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.GtInftySup.policy_gradient_theorem)

无偏优势估计：[Lean 4](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.All_Differentiable_Prob.GtInftySup.unbiased_advantage_estimate)，广义优势估计：[Lean 4](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.All_Differentiable_Prob.GtInftySup.generalized_advantage_estimate)

# 摘要

线性链条件随机场（CRF）用于序列标注，近端策略优化（PPO）用于带反馈的强化学习，乍看是 NLP 里互不相干的两个角落。我们围绕三个结果组织一份 Lean 4 的说明：线性链 CRF 的前向与后向传播、Bellman 方程，以及策略梯度定理及其 REINFORCE 与广义优势估计（GAE）形式。三者依赖同一个装置：马尔可夫结构把对指数多条路径（或无穷视野）的求和变成一步递推，对 CRF 配分函数是前向地跑，对后缀和与价值函数是后向地跑。我们明确说出哪些被 Lean 4 + mathlib 机器检查过。

CRF 一侧，我们形式化了：对数得分分解为转移项与发射项、log-sum-exp 形式的前向递推及 \(-\log p(y\mid x)=\log Z(x)-\text{score}(x,y)\)、Viterbi 的 max-plus 递推（只有最大值），以及离散隐马尔可夫模型的HMM 恒等式：观测序列的似然等于在任一切分点上对隐状态求和的“前向概率乘后向概率”，因而与切分点无关。强化学习一侧，我们形式化了状态与动作空间有限的折扣马尔可夫决策过程（MDP）及其轨迹测度、Bellman 方程、对时间跨度归纳的策略梯度定理（截断、动作价值与 REINFORCE 三种形式）、使基线消失的零均值得分恒等式、无偏折扣优势估计，以及对精确价值函数、所有 \(\lambda\in[0,1]\) 的 GAE。

# 1 引言

用线性链 CRF [10][28] 做序列标注，与用 PPO [25][32][19] 做基于人类反馈的强化学习（RLHF），通常被放在不同的章节里讲。前者是监督学习：已观测的句子 \(x\) 被映射成同样长度的标签序列 \(y\)，目标是最大化 \(\log p(y\mid x)\)。后者是强化学习算法：语言模型逐个生成词元，标量奖励评判整段文本，策略用裁剪的策略梯度步更新。本文讨论两者共有什么，依据是我们在 `lemma` 库 [15] 里，用 Lean 4 [6] 和 [mathlib](https://leanprover-community.github.io/mathlib4_docs/) [16][17] 已经证明了什么。

**三个核心主题** 本文围绕三个结果组织，每个都有自己的一节和自己的 Lean 陈述。

1. **线性链 CRF 的前向与后向传播**（第 5 节）。前向递推 \(z_{t+1}(a)=\sum_bz_t(b)\,\psi_{t+1}(b,a)\)（\(\psi_t\) 为链的单步权重）用 \(O(mk^2)\) 次运算算出配分函数 \(Z\)，而不是对 \(k^{m+1}\) 条标签路径求和；后向递推 \(\beta_t(a)=\sum_c\psi_{t+1}(a,c)\,\beta_{t+1}(c)\) 概括后缀，\(z_t(a)\beta_t(a)\) 是经过时刻 \(t\) 的标签 \(a\) 的全部标签路径的总权重，即后验边缘分布的分子（这是第 6.3 节的概念图景，Lean 陈述见下）。Lean 里有：隐马尔可夫条件情形的、满足 \(-\log p(y\mid x)=\log Z-\text{score}\) 的前向递推，Viterbi 的数值递推，以及离散隐马尔可夫模型的HMM 恒等式：观测序列的似然等于在任一切分点上对隐状态求和的前向概率乘后向概率。
2. **Bellman 方程**（第 6 节）。对状态与动作空间有限的折扣 MDP，价值函数满足 \(V_t(s_t)=\mathbb E[{\color{red}r}_t+\gamma V_{t+1}({\color{magenta}s}_{t+1})\mid{\color{red}s}_t=s_t]\)，动作价值 \(Q_t\) 同理；Lean 对 MDP 的轨迹测度证明了这一点。
3. **策略梯度定理、REINFORCE 与 GAE**（第 7 节）。\(\nabla\mathbb E[\sum_t{}'\,\gamma^t{\color{red}r}_t]=\mathbb E[\sum_t{}'\,\gamma^tG_t\nabla\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)]\) 由对时间跨度的归纳证明，带有显式余项的有限视野恒等式；把 \(G_t\) 换成无偏优势，或换成由精确价值函数构造的广义优势 \(\hat A^\lambda_t\)，梯度不变。

第 8 节是序列标注对序列到序列生成的简短概念性对比，不是定理。

**共同的线索** 本文每个模型里，长度为 \(n\) 的对象的概率都是单步因子的乘积（马尔可夫假设），所以它的对数是逐步项之和：CRF 得分、轨迹的对数概率、语言模型下句子的对数似然。由此用到两个推论。第一，对指数多条路径的求和可以用一步递推计算：CRF 的前向与后向递推是 sum-product 动态规划（Viterbi 是它的 max-sum 版本），Bellman 递推是同样形状的期望递推，沿时间向后跑（第 6.3 节）。我们把这当作类比，而不是定理：没有任何 Lean 陈述把 CRF 递推与 Bellman 递推联系起来。第二，当每个单步因子的和为 1 时，\(\sum_ap(a)=1\) 蕴含 \(\mathbb E_{a\sim p}[\nabla\log p(a)]=0\)，这正是策略梯度可以减去基线而不改变的原因（第 7.2 节）。

**贡献**

1. CRF 传播（第 4、5 节）：对数得分 [crf.markov.logits](http://www.lemma.cn/lean/?module=Tensor.Eq.of.Ne_0.Eq.Eq.Eq.Eq_log.Eq_log.Eq_log) 与 [crf.logits](http://www.lemma.cn/lean/?module=Tensor.Imp.of.Eq)，满足 \(-\log p(y\mid x)=\log Z-\text{score}\) 的前向递推 [CRF loss function](http://www.lemma.cn/lean/?module=Random.All_Eq_AddLogSumExpAdd.All_EqNegLogProb.of.All_Eq_Log.All_Eq_Sum_Exp.All_Eq_LogProbCond.All_Eq_LogProbCond.All_Eq_LogProbJoint.All_Lt0Prob.IsDiscreteHMM)，Viterbi 数值递推 [crf.viterbi](http://www.lemma.cn/lean/?module=Random.All_Eq_Add_MaxAdd.EqMax_ProbJoint.of.All_Eq_Max.Eq_LogProbCond.Eq_LogProbCond.Eq_LogProbJoint.All_Lt0ProbJoint.IsDiscreteHMM)，以及HMM 恒等式 [hmm_identity](http://www.lemma.cn/lean/?module=Random.Sum_Mul_ProbCond.eq.Prob.of.IsDiscreteHMM)，针对离散隐马尔可夫模型。
2. Bellman 方程 [Bellman](http://www.lemma.cn/lean/?module=Random.Eq_Expect.Eq_Expect.Eq_Expect.of.All_Eq_Expect.All_Eq_Expect.In_Ico)，建立在轨迹层面的 MDP 上，其轨迹律的马尔可夫性是已证明的（[joint_succ](http://www.lemma.cn/lean/?module=Random.Map)、[hist_step](http://www.lemma.cn/lean/?module=Random.Integral.eq.Integral_Integral.of.All_LeNorm.StronglyMeasurable.history)）（第 6 节）。
3. 对时间跨度归纳证明的策略梯度定理，截断、动作价值与 REINFORCE 三种形式（[policy_gradient_theorem](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.GtInftySup.policy_gradient_theorem)）；无偏优势估计 [unbiased_advantage_estimate](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.All_Differentiable_Prob.GtInftySup.unbiased_advantage_estimate)；以及对精确价值函数、所有 \(\lambda\in[0,1]\) 的 GAE [generalized_advantage_estimate](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.All_Differentiable_Prob.GtInftySup.generalized_advantage_estimate) 及其加权平均形式（第 7 节）。
4. 两张对比表（第 9 节）。

库里为极限、期望与概率设计的教科书语法糖，让 Lean 陈述读起来像论文里的公式，在第 3 节概述。

# 2 相关工作

**HMM、MEMM 与 CRF** 隐马尔可夫模型（HMM）[21] 是生成式的：它对联合分布 \(p(x,y)=\prod_tp(y_t\mid y_{t-1})\,p(x_t\mid y_t)\) 建模，各因子局部归一化。最大熵马尔可夫模型（MEMM）[18] 是判别式的，但仍是局部归一化，\(\prod_tp(y_t\mid y_{t-1},x)\)，并有 label bias 问题；条件随机场 [10] 用一个对整条标签序列的配分函数 \(Z(x)\) 做全局归一化，去掉了这个问题。Sutton 与 McCallum [28] 给出了标准的教程式处理，包括前向、后向与 Viterbi 递推。神经 CRF 把神经网络放在一元得分之下：Collobert 等人 [5] 用带转移得分的句子级似然训练，Huang 等人 [8]、Lample 等人 [11] 与 Ma 与 Hovy [14] 在 BiLSTM 编码器上加 CRF 层，Andor 等人 [1] 主张全局归一化的基于转移的神经网络。苏剑林在“科学空间”的博客文章给出了简明的中文推导：CRF 损失及其递归的归一化项 [27]；面向 NER 的、可替代 CRF 的基于片段的方法是 GlobalPointer [29]；更多与 CRF 相关的文章列在站点的[搜索页](https://spaces.ac.cn/search/CRF/) [30]。

**序列到序列模型与 exposure bias** 神经序列到序列模型 [31][2][36] 把 \(p(y\mid x)=\prod_tp(y_t\mid x,y_{<t})\) 分解开，训练时用真实前缀（教师强制），解码时却用自己生成的前缀；这个不匹配叫 exposure bias，对策有 scheduled sampling [3]、序列级训练 [22] 与 beam-search 优化 [38]。

**策略梯度、GAE 与 PPO** 策略梯度定理出自 Sutton 等人 [33]，似然比估计与强化基线来自 Williams [37]；Greensmith、Bartlett、Baxter [7] 把基线当作方差缩减手段做了分析。Schulman 等人 [23] 提出 GAE，当时与信赖域策略优化（TRPO）[24] 配合使用；TRPO 早于 GAE，并没有定义它。PPO [25] 用裁剪的替代目标取代信赖域约束，并用截断（有限视野）的 GAE 计算优势，即其公式 (10)–(11)。语言模型的 RLHF [32][19] 在词元上运行 PPO，使用奖励模型得分和对参考模型的 KL 惩罚，GRPO [26] 是去掉学习得到的 critic 的 PPO 变体。有限 MDP 的标准参考文献是 Puterman [20] 以及 Sutton 与 Barto [34]。

**形式化方面** CertRL [35] 在 Coq 里形式化了值迭代与策略迭代的收敛，[Chevallier 与 Fleuriot](https://arxiv.org/abs/2112.05996) [4] 在 Isabelle/HOL 里形式化了带奖励的有限 MDP，包括 Bellman 方程、\(\gamma<1\) 时最优策略的存在性，以及值迭代与策略迭代；两者都没有涉及策略梯度。在 Lean 4 里，[TorchLean](https://github.com/lean-dojo/TorchLean) [13] 证明了关于 MDP 与 Bellman 算子的结构性和动态规划性质，并含有策略梯度与 PPO 的训练代码，但没有策略梯度定理。与第 7 节最接近的是 Zhang 的 `rl-theory-in-lean` 中的 `PolicyGradient` 模块 [rl-theory-in-lean](https://github.com/ShangtongZhang/rl-theory-in-lean/commit/2a9d01a236961b1c9bc451a8926346364fc66e7f) [39]，这是一套实验性的、主要由机器生成的开发（其提交与 AI 助手共同署名），2026 年 3 月提交，后来从该项目的 main 分支撤回，在所引用的提交处仍可访问。对有限的状态和动作空间、带有限个实参数的策略，它证明了占用测度形式

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

**颜色** lemma.cn 的渲染器把每条陈述排成 LaTeX，并按概率角色给标识符上色：{\color{red}红色}是随机变量（样本空间上的函数、\(\mathbb E\) 绑定式里被积掉的变量、\(\mathbb P\) 事件里 `=` 左边的变量），{\color{magenta}品红}是随机自变量（作为函数自变量的随机变量，使整个表达式本身是随机的），黑色是观测值。我们沿用这一约定：\({\color{red}s}_t,{\color{red}a}_t,{\color{red}r}_t\) 是红色，\(s_t,a_t,x,u,y\) 是取值。

**零概率事件与极限** 由于 \(\mu[\,\cdot\mid B]=\mu(B)^{-1}\mu|_B\) 在 \(\mu(B)=0\) 时是零测度，在不可达状态上的条件期望是 \(0\)；因此关于价值函数的假设限制在**可达**取值 \(s_t\)，即 \(\mathbb P_\theta({\color{red}s}_t=s_t)\ne0\) 的那些。无穷和是 Lean 的 `tsum`（可和族的和，否则为 \(0\)），每个极限都是显式的 `Filter.Tendsto` 陈述。我们陈述的唯一极限引理如下，用于截断策略梯度的余项（第 7 节）。

**引理 3.1（[Lim.of.LtAbs.GtInftySup](http://www.lemma.cn/lean/?module=Real.Eq_0.Lim.of.LtAbs.GtInftySup)）** 设 \(\gamma\in\mathbb R\)，\(x:\mathbb N\to\mathbb R\)，\(|\gamma|<1\) 且 \(\{|x_n|:n\in\mathbb N\}\) 有上界。则

\[
\lim_{n\to\infty}\gamma^n x_n=0.
\]

# 4 Lean 中的马尔可夫假设

**共同性质** 无论哪种应用，一阶马尔可夫假设都说：长度为 \(n\) 的对象的概率是 \(n\) 个单步因子的乘积，每个因子在合适的状态空间里只回看有限的一步。本文处处用到两个推论：（i）乘积的对数是各因子对数之和，所以得分是逐步项之和；（ii）乘积可以按长度归纳地构造、求和、取最大或求导，这给出线性时间的递推。模型之间的差别是因子如何归一化（第 9 节）。

对隐马尔可夫模型和决策过程，这个乘积是同一个分解，只是角色分别是（标签，观测）与（状态，动作）：两者是同一个 Lean 模块 [Markov 乘积定理](http://www.lemma.cn/lean/?module=Random.ProbJoint.eq.Mul_Prod_MulProbSCond.of.IsDiscreteHMM) 里的两个声明（后者是 `crf.markov.mdp`）。

## 4.1 条件独立：标准构件

库里有三条引理，形式化了通常用来陈述马尔可夫假设的条件独立词汇。设 \(x,y,z\) 是概率空间上的可测随机变量。

- [CondIndep.of.Indep_Joint](http://www.lemma.cn/lean/?module=Random.CondIndep.of.Indep_Joint)：若 \(x\perp(y,z)\)，则 \(x\perp y\mid z\)。
- [Indep_Joint.of.CondIndep.Indep](http://www.lemma.cn/lean/?module=Random.Indep_Joint.of.CondIndep.Indep)：若 \(z\perp x\mid y\) 且 \(z\perp y\)，则 \(z\perp(x,y)\)。
- [All_Imp_EqProbSCond.of.CondIndep](http://www.lemma.cn/lean/?module=Random.All_Imp_EqProbSCond.of.CondIndep)：若 \(x\perp y\mid z\)，则在参考测度几乎处处，只要 \(\mathbb P(y,z)\ne0\)，就有 \(\mathbb P(x\mid y,z)=\mathbb P(x\mid z)\)；这就是条件形式的马尔可夫性。

把联合概率逐个变量分解的链式法则，是离散引理 [ProbCond.eq.Mul.ProbCond](http://www.lemma.cn/lean/?module=Random.ProbCond.eq.Mul.ProbCond)：对值域可数、参考测度为计数测度的变量，\(\mathbb P(x\wedge y\mid z)=\mathbb P(x\mid z)\,\mathbb P(y\mid x\wedge z)\)。它是两变量、逐点的，并化归为条件独立的测度形式 [MulMeasure.eq.MulMeasure.of.CondIndep](http://www.lemma.cn/lean/?module=Random.MulMeasure.eq.MulMeasure.of.CondIndep)，\(\mathbb P(x{=}u,y{=}v,z{=}w)\,\mathbb P(z{=}w)=\mathbb P(x{=}u,z{=}w)\,\mathbb P(y{=}v,z{=}w)\)（由上面第三条引理得到，无需非零假设），以及把 \(\mathbb P(x\mid y)\) 等同于测度之比的 [ProbCond.eq.Div.of.Eq_Count.Eq_Count](http://www.lemma.cn/lean/?module=Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count)。

# 5 线性链 CRF 的前向与后向传播

这是第一个核心主题。线性链 CRF 给标签序列 \(ys\in\mathcal Y^{m+1}\) 一个权重，它是单步因子的乘积，配分函数 \(Z\) 是这些权重在全部 \(k^{m+1}\) 个标签序列上的和。马尔可夫结构使两个和能在线性时间内算出：对前缀的**前向**递推（第 5.2 节）与对后缀的**后向**递推；同一条链上把 \(\sum\) 换成 \(\max\) 的第三个递推就是 Viterbi（第 5.3 节）。第 5.2 节与第 5.3 节针对隐马尔可夫条件特例在对数域陈述。

## 5.1 从乘积到得分

记 \(G(a,b)=\log\mathbb P(y_{i+1}=a\mid y_i=b)\) 为从 \(b\) 到 \(a\) 的转移得分，\(e_t(a)=\log\mathbb P(x_t=xo_t\mid y_t=a)\) 为发射（一元）得分，\(s_t(ys)=\log P_t(ys)\) 为标签前缀的对数得分，其中对固定的观测序列 \(xo\) 与标签序列 \(ys:\mathbb N\to\mathcal Y\)，\(P_t(ys)=\mathbb P\bigl(x[{:}t{+}1]=xo[{:}t{+}1]\wedge y[{:}t{+}1]=ys[{:}t{+}1]\bigr)\) 是前 \(t+1\) 个观测与标签的联合概率。下面的陈述中所有概率都假设严格为正。

**定理 5.1（[crf.markov.logits](http://www.lemma.cn/lean/?module=Tensor.Eq.of.Ne_0.Eq.Eq.Eq.Eq_log.Eq_log.Eq_log)）** 若前缀概率满足一步隐马尔可夫分解 \(P_{t+1}(ys)=P_t(ys)\cdot T(ys_t,ys_{t+1})\cdot E_{t+1}(ys_{t+1})\)，且 \(P,T,E>0\)（其中 \(T(a,b)\) 读作 \(\mathbb P(y_{i+1}=b\mid y_i=a)\)，\(E_i(b)\) 读作 \(\mathbb P(x_i=xo_i\mid y_i=b)\)），\(s_t=\log P_t\)，\(x_t=\log E_t\)，\(G(a,b)=\log T(b,a)\)。则对每个 \(t>0\)，

\[
s_t(ys)=G(ys_t,ys_{t-1})+s_{t-1}(ys)+x_t(ys_t).
\]

**定理 5.2（[crf.logits](http://www.lemma.cn/lean/?module=Tensor.Imp.of.Eq)）** 设 `IsHiddenMarkovPr π x y xo`，\(\mathbb P(y_0=a)\)、\(\mathbb P(y_{i+1}=a\mid y_i=b)\)、\(\mathbb P(x_t=xo_t\mid y_t=a)\) 为正，且 \(s_t,e_t,G\) 如上。则对每个 \(ys\)，

\[
\begin{aligned}
s_{t+1}(ys)&=G(ys_{t+1},ys_t)+s_t(ys)+e_{t+1}(ys_{t+1}),\\
s_t(ys)&=\log\mathbb P(y_0=ys_0)+\sum_{i=1}^{t}G(ys_i,ys_{i-1})+\sum_{i=0}^{t}e_i(ys_i).
\end{aligned}
\]

第二行就是教科书上线性链 CRF 的得分：一元（发射）项与二元（转移）项之和。它恰是第 4 节的**马尔可夫乘积的对数是逐步项之和**这一性质；神经 CRF [8][11][14] 把 \(e_t\) 换成网络输出、把 \(G\) 当作自由矩阵，苏剑林的推导 [27][27] 也从同一个加性形式出发。

## 5.2 CRF 损失函数

设 \(\mathcal Y\) 有限、含 \(k\) 个元素，固定长度 \(m+1\)，令 \(z_t(a)=\sum_{ys\in\mathcal Y^{t+1},\;ys_t=a}e^{s_t(ys)}\)，\(\alpha_t(a)=\log z_t(a)\)。

**定理 5.3（[CRF loss function](http://www.lemma.cn/lean/?module=Random.All_Eq_AddLogSumExpAdd.All_EqNegLogProb.of.All_Eq_Log.All_Eq_Sum_Exp.All_Eq_LogProbCond.All_Eq_LogProbCond.All_Eq_LogProbJoint.All_Lt0Prob.IsDiscreteHMM)）** 在定理 5.2 的假设下（前缀概率为正），

\[
\alpha_{t+1}(a)=\log\sum_{b\in\mathcal Y}\exp\bigl(\alpha_t(b)+G(a,b)\bigr)+e_{t+1}(a),
\]

并且对每个标签序列 \(ys\)，

\[
-\log\mathbb P\bigl(y[{:}m{+}1]=ys[{:}m{+}1]\bigm|x[{:}m{+}1]=xo[{:}m{+}1]\bigr)\;=\;\log\sum_{b\in\mathcal Y}e^{\alpha_m(b)}\;-\;s_m(ys).
\]

## 5.3 Viterbi：max-plus 递推

把和换成最大值、把对数换成恒等映射，得到第二个递推。令 \(v_t(a)=\max_{ys\in\mathcal Y^{t+1},\,ys_t=a}s_t(ys)\)。

**定理 5.4（[crf.viterbi](http://www.lemma.cn/lean/?module=Random.All_Eq_Add_MaxAdd.EqMax_ProbJoint.of.All_Eq_Max.Eq_LogProbCond.Eq_LogProbCond.Eq_LogProbJoint.All_Lt0ProbJoint.IsDiscreteHMM)）** 在同样的假设下，

\[
\begin{aligned}
v_{t+1}(a)&=e_{t+1}(a)+\max_{b\in\mathcal Y}\bigl(v_t(b)+G(a,b)\bigr),\\
\max_{ys\in\mathcal Y^{m+1}}\mathbb P\bigl(x[{:}m{+}1]=xo[{:}m{+}1]&\wedge y[{:}m{+}1]=ys\bigr)=\exp\max_{b\in\mathcal Y}v_m(b).
\end{aligned}
\]

只算出了最大**值**；没有 argmax 也没有回溯指针，所以解码出的序列本身没有形式化。苏剑林 [27] 读出了同样的两个递推，分别用于训练与预测。

## 5.4 HMM 对 CRF：陈述说了什么、没说什么

**HMM** 隐马尔可夫模型 [21] 是**生成式**、**局部归一化**的：

\[
p(x,y)=\prod_{t}p(y_t\mid y_{t-1})\,p(x_t\mid y_t),\qquad Z=1,
\]

每个因子在自己的变量上都是概率分布。

**线性链 CRF** 线性链 CRF [10][28] 是**判别式**、**全局归一化**的：

\[
p(y\mid x)=\frac1{Z(x)}\prod_{t}\psi_t(y_{t-1},y_t,x),\qquad Z(x)=\sum_{y'\in\mathcal Y^{n}}\prod_t\psi_t(y'_{t-1},y'_t,x),
\]

势函数 \(\psi_t\) 是任意非负函数，不必是概率；配分函数 \(Z(x)\) 只有一个，是对 \(k^n\) 条标签路径的和。马尔可夫假设使 \(Z(x)\) 能用前向递推计算，而 HMM 恒等式把似然在任一切分点拆成前向概率与后向概率。就定理 5.2 的得分递推而言，CRF 就是去掉了局部归一化约束的 HMM 得分递推：势函数 \(\psi_t=e^{G+e_t}\) 是自由的，剩下的概率是 \(e^{\text{score}}/Z(x)\)。

# 6 Bellman 方程

这是第二个核心主题。CRF 引理固定一个已观测的句子并对标签求和；这里随机的是整条轨迹，马尔可夫结构是决策过程的：下一个状态与奖励对过去的依赖只通过当前状态与动作。Bellman 方程说，一个状态的价值是即时奖励的期望加上下一状态折扣后的价值，这是一个一步递推，它代替了无穷视野的期望。

## 6.1 模型与轨迹测度

**定义 6.1（模型）** 设 \(S\)、\(A\) 是带离散 \(\sigma\)-代数的有限类型，\(\Theta\) 是实赋范空间。**策略**是函数 \(\pi:\Theta\to S\to A\to\mathbb R\)，记作 \(\pi_\theta(u\mid x)\)，满足 \(\pi_\theta(u\mid x)\ge0\)、\(\sum_u\pi_\theta(u\mid x)=1\)（局部归一化：每一步 \(Z=1\)）。**环境**由 \(S\) 上的初始概率测度 \(\iota\)、从 \(S\times A\) 到 \(S\) 的马尔可夫核 \(T\)、从 \(S\times A\) 到 \(\mathbb R\) 的马尔可夫核 \(R\)（奖励律，支撑在 \([-R_{\max},R_{\max}]\) 内）组成。

一条轨迹是阶段序列 \(\omega\in(S\times A\times\mathbb R)^{\mathbb N}\)，坐标记为 \({\color{red}s}_t,{\color{red}a}_t,{\color{red}r}_t\)。从状态 \(x\) 出发走一步由核 \(\kappa_\theta(x)=\delta_x\otimes(\pi_\theta(\cdot\mid x)\otimes R)\) 给出，阶段链的核是 \(K_\theta(x,u,\rho)=(\kappa_\theta\circ T)(x,u)\)。轨迹测度 \(\mathbb P_\theta=\mathtt{Kernel.trajMeasure}\;\mu_0\;(K_\theta)_n\) 是 mathlib 提供的 Ionescu-Tulcea 扩张 [9]，其中第 \(n\) 个核只看历史的最后一个阶段。

有限维边缘分布具有马尔可夫乘积的形状 \(\iota(s_0)\prod_t\pi_\theta(a_t\mid s_t)\,T(s_{t+1}\mid s_t,a_t)\,R(\cdot\mid s_t,a_t)\)。它的对数是逐步项之和，而转移与奖励因子不依赖于 \(\theta\)，所以**轨迹的得分是各个动作得分之和**，\(\sum_t\nabla_\theta\log\pi_\theta(a_t\mid s_t)\)。这是定理 5.2 中 CRF 得分在 MDP 里的对应物；Lean 只通过下面的期望引理 `E_score` 用到它。

**这里马尔可夫性是定理** \(\mathbb P_\theta\) 的马尔可夫性不是假设，而是由构造证出来的。轨迹引理包括 [joint_succ](http://www.lemma.cn/lean/?module=Random.Map)：\((\omega_t,\omega_{t+1})\) 的分布是 \(\omega_t\) 的分布与核 \(K_\theta\) 的复合；以及 [hist_step](http://www.lemma.cn/lean/?module=Random.Integral.eq.Integral_Integral.of.All_LeNorm.StronglyMeasurable.history)：对有界可测的 \(\varphi\)，

\[
\mathbb E\bigl[\varphi(h_n,\omega_{n+1})\bigr]=\int\Bigl(\int\varphi(h,z)\,dK_\theta(\mathrm{last}\,h)(z)\Bigr)\,d\,\mathrm{law}(h_n)(h),
\]

其中 \(h_n=(\omega_0,\dots,\omega_n)\) 是历史，\(\mathrm{last}\,h\) 是它的最后一个阶段；下面还用到它们的迭代版本（[hist_mul](http://www.lemma.cn/lean/?module=Random.Integral_Mul.eq.Integral_Mul_Integral.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable)、[hist_iter](http://www.lemma.cn/lean/?module=Random.All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable)）。状态与动作的联合律分解为 \(\mathbb P(s_t=x,a_t=u)=\mathbb P(s_t=x)\,\pi_\theta(u\mid x)\)（[ProbJoint.eq.Mul_Prob_Pr](http://www.lemma.cn/lean/?module=Random.ProbJoint.eq.Mul_Prob_Pr)）。

## 6.2 价值函数与 Bellman 方程

对 \(\gamma\in[0,1)\)，从 \(t\) 起的折扣回报是 \(G_t=\sum_k{}'\,\gamma^k{\color{red}r}_{t+k}\)，\(V_t^\theta(s_t)=\mathbb E_\theta[G_t\mid{\color{red}s}_t]\)，\(Q_t^\theta(s_t,a_t)=\mathbb E_\theta[G_t\mid{\color{red}s}_t,{\color{red}a}_t]\)。目标函数是 \(J(\theta)=\mathbb E_\theta[\sum_t{}'\,\gamma^t{\color{red}r}_t]=\sum_t{}'\,\gamma^t\mathbb E_\theta[{\color{red}r}_t]\)。轨迹引理证明了：在可达状态上 \(V_t^\theta\) 等于一个与时间无关的闭式（[V_eq](http://www.lemma.cn/lean/?module=Random.V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico)），\(|V_t|,|Q_t|\le(1-\gamma)^{-1}R_{\max}\)，并且对可微且梯度一致有界的策略，\(J\) 是 Fréchet 可微的。我们始终假设：(D) \(\gamma\in[0,1)\)；(P1) \(\theta\mapsto\pi_\theta(u\mid x)\) 可微；(P2) \(\sup_{\theta,x,u}\|\nabla_\theta\pi_\theta(u\mid x)\|<\infty\)。对 \(V_t\) 与 \(\nabla V_t\) 的界是推出来的，不是假设。

**定理 6.2（Bellman 方程 [Bellman](http://www.lemma.cn/lean/?module=Random.Eq_Expect.Eq_Expect.Eq_Expect.of.All_Eq_Expect.All_Eq_Expect.In_Ico)）** 设 (D) 成立，\(V\)、\(Q\) 满足 \(V_t(s_t)=\mathbb E_\theta[G_t\mid{\color{red}s}_t]\)、\(Q_t(s_t,a_t)=\mathbb E_\theta[G_t\mid{\color{red}s}_t,{\color{red}a}_t]\)。则

\[
\begin{aligned}
V_t(s_t)&=\mathbb E_\theta\bigl[Q_t(s_t,{\color{red}a}_t)\bigm|{\color{red}s}_t\bigr],\\
V_t(s_t)&=\mathbb E_\theta\bigl[{\color{red}r}_t+\gamma\,V_{t+1}({\color{magenta}s}_{t+1})\bigm|{\color{red}s}_t\bigr],\\
Q_t(s_t,a_t)&=\mathbb E_\theta\bigl[{\color{red}r}_t+\gamma\,V_{t+1}({\color{magenta}s}_{t+1})\bigm|{\color{red}s}_t,\ {\color{red}a}_t\bigr].
\end{aligned}
\]

在 Lean 文件里，三个恒等式对每个 \(t\) 与每一对 \((x,u)\) 都成立，没有可达性假设：在零概率的条件事件上两边都是 \(0\)（第 3 节）。从 \(t+1\) 到 \(t\) 读，第二个恒等式是价值函数的**后向**递推，方向与 CRF 的后向递推相同；第 6.3 节比较两者，但不声称有定理。这个递推的梯度是策略梯度定理的第一步（定理 7.1）。

## 6.3 前向、后向与 Bellman 递推并排（类比）

本小节是类比，不是定理：没有任何 Lean 陈述把 CRF 递推与 Bellman 递推联系起来。表 1 列出本文的四个一步递推、各自在马尔可夫链上做的聚合、运行方向，以及证明它的 Lean 陈述。这里 \(z_t\) 与 \(\beta_t\) 是带单步权重 \(\psi_t\) 的链的前向与后向变量：\(z_0=\psi_0\)，\(z_{t+1}(a)=\sum_bz_t(b)\,\psi_{t+1}(b,a)\)，以及 \(\beta_m=1\)，\(\beta_t(a)=\sum_c\psi_{t+1}(a,c)\,\beta_{t+1}(c)\)。对隐马尔可夫模型，\(\psi_{t+1}(b,a)=\mathbb P(y_{t+1}=a\mid y_t=b)\mathbb P(x_{t+1}=xo_{t+1}\mid y_{t+1}=a)\)，\(z_t(a)\) 与 \(\beta_t(a)\) 就是 HMM 恒等式中的前向与后向概率。这些变量只用于本节的比较；这些递推本身不是 Lean 陈述，只有前向递推的对数形式（定理 5.3）与 Viterbi 的数值递推（定理 5.4）例外。

| 递推 | 一步 | 方向 | 聚合 | Lean |
|---|---|---|---|---|
| CRF 前向 | \(z_{t+1}(a)=\sum_bz_t(b)\,\psi_{t+1}(b,a)\) | 沿 \(t\) 向前 | 对前缀求和（sum-product） | 对数形式见定理 5.3 |
| CRF 后向 | \(\beta_t(a)=\sum_c\psi_{t+1}(a,c)\,\beta_{t+1}(c)\) | 沿 \(t\) 向后 | 对后缀求和（sum-product） | 不是 Lean 陈述 |
| Viterbi | \(v_{t+1}(a)=e_{t+1}(a)+\max_b\bigl(v_t(b)+G(a,b)\bigr)\) | 沿 \(t\) 向前 | 对前缀取最大（max-sum） | 定理 5.4（只有数值） |
| Bellman | \(V_t(s_t)=\mathbb E_\theta[{\color{red}r}_t+\gamma V_{t+1}({\color{magenta}s}_{t+1})\mid{\color{red}s}_t]\) | 沿 \(t\) 向后 | 对下一状态与奖励取期望 | 定理 6.2 |

表 1：马尔可夫链上的一步递推。前三个是对标签路径的动态规划；Bellman 递推是对轨迹的动态规划。

形式上，若在 Bellman 递推里去掉奖励并给定终端价值，它就变成 \(V_t(s)=\sum_cK(s,c)\,V_{t+1}(c)\)，其中 \(K\) 是状态链的一步核，形状恰与后向递推 \(\beta_t(a)=\sum_c\psi_{t+1}(a,c)\beta_{t+1}(c)\) 相同，对应 \(\psi\leftrightarrow K\)、\(\beta_m\leftrightarrow V_m\)。差别是真实的：\(K\) 是概率核（\(\sum_cK(s,c)=1\)），而 \(\psi\) 是未归一化的权重；Bellman 递推带有奖励源项与折扣；Lean 里的价值函数是无穷视野的条件期望，不是有限后缀和。这些递推共有的是机制：马尔可夫结构把全局求和换成一步递推，当量由过去构成时向前，由未来构成时向后。

# 7 策略梯度定理：REINFORCE 与 GAE

这是第三个核心主题。策略梯度定理把折扣回报期望的梯度表示成回报乘以实际所取动作的得分 \(\nabla\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\) 的期望。Lean 由 Bellman 递推出发对时间跨度归纳来证明它，有三种形式：带显式余项的截断形式（定理 7.2）、动作价值形式，以及 REINFORCE 形式（定理 7.3）。由于局部归一化使得分零均值（引理 7.4），回报可以换成优势，这给出无偏优势估计与 GAE（第 7.3 节）。

## 7.1 归纳法证明策略梯度定理

**定理 7.1（递推 [policy_gradient.recursion.discrete](http://www.lemma.cn/lean/?module=Random.Grad.eq.Add_SMul_Sum_SMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.All_Eq_Expect.All_Eq_Expect.EqMeasureCount.EqMeasureCount.In_Ico)，展开 [policy_gradient.induct](http://www.lemma.cn/lean/?module=Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.induct)）** 设 (D)、(P1)、(P2) 成立，\(s_0\) 可达。则在可达的 \(s_t\) 上 \(\nabla V_t(s_t)=\sum_uQ_t(s_t,u)\nabla\pi_\theta(u\mid s_t)+\gamma\sum_y\mathbb P_\theta({\color{red}s}_{t+1}=y\mid{\color{red}s}_t)\nabla V_{t+1}(y)\)，并且对每个 \(n\)，

\[
\nabla_\theta V_0(s_0)=\sum_{t<n}\gamma^t\sum_y\mathbb P_\theta({\color{red}s}_t=y\mid{\color{red}s}_0)\sum_uQ_t(y,u)\nabla_\theta\pi_\theta(u\mid y)+\gamma^n\sum_y\mathbb P_\theta({\color{red}s}_n=y\mid{\color{red}s}_0)\nabla_\theta V_n(y).
\]

**定理 7.2（截断策略梯度 [policy_gradient](http://www.lemma.cn/lean/?module=Tensor.Eq.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient)）** 设 (D)、(P1)、(P2) 成立。则对每个 \(n\in\mathbb N\)，

\[
\sum_t{}'\,\gamma^t\nabla_\theta\mathbb E_\theta[{\color{red}r}_t]=\mathbb E_\theta\Bigl[\sum_{t<n}\gamma^tQ_t({\color{magenta}s}_t,{\color{magenta}a}_t)\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\Bigr]+\gamma^n\,\mathbb E_\theta\bigl[\nabla_\theta V_n({\color{magenta}s}_n)\bigr].
\]

虽然是有限和，该定理讨论的仍是折扣无穷视野目标：它对每个截断层级都精确成立，带显式余项。令 \(n\to\infty\)，余项由引理 3.1 和对 \(\nabla V_n\) 在可达状态上的界趋于 \(0\)，得到动作价值形式 [GtInftySup.Q_Function](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.GtInftySup.Q_Function)：\(\sum_t{}'\,\gamma^t\nabla_\theta\mathbb E_\theta[{\color{red}r}_t]=\sum_t{}'\,\gamma^t\mathbb E_\theta[Q_t({\color{magenta}s}_t,{\color{magenta}a}_t)\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)]\)；再用塔性质 [Q_Function.discounted](http://www.lemma.cn/lean/?module=Tensor.Eq.Expect.Grad.Log.Pr.of.Eq_Conditioned.Q_Function.discounted)，\(\mathbb E_\theta[G_t\nabla_\theta\log\pi_\theta]=\mathbb E_\theta[Q_t\nabla_\theta\log\pi_\theta]\)，得到 REINFORCE 形式。

**定理 7.3（策略梯度，REINFORCE 形式 [policy_gradient_theorem](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.GtInftySup.policy_gradient_theorem)）** 设 \(\Theta\) 是实 Hilbert 空间，\(S\)、\(A\) 以计数测度为参考测度，(D)、(P1)、(P2) 成立。则

\[
\nabla_\theta\mathbb E_\theta\Bigl[\sum_t{}'\,\gamma^t{\color{red}r}_t\Bigr]=\mathbb E_\theta\Bigl[\sum_t{}'\,\gamma^t\,G_t\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\Bigr].
\]

这里级数在期望之内；这是因为奖励有界，共用引理 [Log.Pr.of.Bounded](http://www.lemma.cn/lean/?module=Tensor.Eq.Expect.Sum.Grad.Log.Pr.of.Bounded) 与 [Log.Pr.of.Bounded.Discount](http://www.lemma.cn/lean/?module=Tensor.Eq.Expect.Sum.Grad.Log.Pr.of.Bounded.Discount) 完成级数与期望的交换。

## 7.2 归一化给出零均值得分

把定义 6.1 的局部归一化与方差缩减联系起来的性质如下。

**引理 7.4（[Expect_ConditionedGrad_LogProb.eq.Zero](http://www.lemma.cn/lean/?module=Random.Expect_ConditionedGrad_LogProb.eq.Zero)）** 设 \(p:\Theta\to A\to\mathbb R\)，对所有 \(\theta'\) 有 \(\sum_ap_{\theta'}(a)=1\)，\(p_\theta(a)>0\)，且 \(\theta'\mapsto p_{\theta'}(a)\) 在 \(\theta\) 可微。则 \(\mathbb E_{a\sim p_\theta}[\nabla_\theta\log p_\theta(a)]=\sum_ap_\theta(a)\nabla_\theta\log p_\theta(a)=0\)。

对轨迹模型里的策略，它的条件形式是 [LogProb.eq.Zero.policy](http://www.lemma.cn/lean/?module=Random.Expect_ConditionedGrad_LogProb.eq.Zero.policy)：对正的可微策略，\(\mathbb E_\theta[\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\mid{\color{red}s}_t=x]=0\)。模型文件里同一事实不需要正性也成立（\(\pi_\theta(u\mid x)=0\) 的项为零）：对每个 \(h:S\to\mathbb R\)，\(\mathbb E_\theta[h({\color{red}s}_t)\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)]=0\)（`E_h_score`）。这就是只依赖状态的基线不改变策略梯度的原因，第 7.3 节用的就是这一步。对全局归一化的 CRF，对应的事实不同：\(\mathbb E_{p(y\mid x)}[\nabla\log p(y\mid x)]=0\) 同样成立，但 \(\nabla\log p=\nabla\text{score}-\mathbb E[\nabla\text{score}]\) 含有配分函数；恒等式 \(\nabla\log Z=\mathbb E[\nabla\text{score}]\) 没有形式化。

## 7.3 无偏优势估计与广义优势估计

记 \(\delta_j={\color{red}r}_j+\gamma V_{j+1}({\color{red}s}_{j+1})-V_j({\color{red}s}_j)\) 为价值函数 \(V\) 的时序差分残差。

**定理 7.5（无偏优势估计 [unbiased_advantage_estimate](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.All_Differentiable_Prob.GtInftySup.unbiased_advantage_estimate)）** 设 \(\Theta\) 是实 Hilbert 空间，\(S\)、\(A\) 以计数测度为参考测度，(D)、(P1)、(P2) 成立，且对所有 \(\theta,t\) 和所有可达 \(s_t\) 有 \(V^\theta_t(s_t)=\mathbb E_\theta[G_t\mid{\color{red}s}_t]\)。令 \(\hat A_t=\sum_k{}'\,\gamma^k\delta_{t+k}\)，则

\[
\nabla_\theta\mathbb E_\theta\Bigl[\sum_t{}'\,\gamma^t{\color{red}r}_t\Bigr]=\mathbb E_\theta\Bigl[\sum_t{}'\,\gamma^t\,\hat A_t\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\Bigr].
\]

对有界的 \(V\)，级数裂项相消为 \(\hat A_t=G_t-V_t({\color{red}s}_t)\)，所以定理 7.5 化归为定理 7.3，加上基线项消失 \(\mathbb E_\theta[V_t({\color{red}s}_t)\nabla_\theta\log\pi_\theta]=0\)（第 7.2 节）。

**定理 7.6（广义优势估计 [generalized_advantage_estimate](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.All_Differentiable_Prob.GtInftySup.generalized_advantage_estimate)）** 在定理 7.5 的假设下，设 \(\lambda\in[0,1]\)，\(\hat A^{\lambda}_t=\sum_k{}'\,(\gamma\lambda)^k\delta_{t+k}\)。则

\[
\nabla_\theta\mathbb E_\theta\Bigl[\sum_t{}'\,\gamma^t{\color{red}r}_t\Bigr]=\mathbb E_\theta\Bigl[\sum_t{}'\,\gamma^t\,\hat A^{\lambda}_t\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\Bigr].
\]

对 \(\lambda\in[0,1)\)，[Schulman 等人](https://arxiv.org/abs/1506.02438) [23] 的加权平均形式 \(\hat A^{\lambda}_t=(1-\lambda)\sum_{k\ge0}\lambda^k\sum_{i\le k}\gamma^i\delta_{t+i}\) 给出同一个恒等式 [In_Ico.generalized_advantage_estimate](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.All_Differentiable_Prob.GtInftySup.In_Ico.generalized_advantage_estimate)，经由级数恒等式 [GtInftySup.generalized_advantage_estimate](http://www.lemma.cn/lean/?module=Tensor.EqDot.of.GtInftySup.generalized_advantage_estimate)。这些陈述针对精确价值函数：用近似的 critic 时，\(k\ge1\) 的项不一定零均值，\(\lambda<1\) 是有偏的 [23]；这一点没有形式化。GAE 是 PPO [25] 所用的优势估计器，PPO 用的是它的截断（有限视野）形式（其公式 (10)–(11)）；PPO 的其余部分（裁剪替代目标、重要性比、KL 惩罚、学习得到的 critic）没有形式化。

# 8 超越核心：从标注到生成（概念性）

本节是比较，不是定理，也不属于三个核心主题。库里没有序列到序列、教师强制、exposure bias 或 label bias 的引理；它有的是比较中要组合的两块砖。

**同一个分子的两种归一化** 设 \(\text{score}(x,y)=\sum_tf_t(y_{<t},y_t;x)\) 是加性得分。**全局归一化**模型令 \(p(y\mid x)=e^{\text{score}(x,y)}/Z(x)\)，\(Z(x)=\sum_{y'}e^{\text{score}(x,y')}\)，故 \(-\log p=\log Z(x)-\text{score}(x,y)\)；对线性链，前向递推精确地算出 \(Z\)。**局部归一化**模型对每一步用自己的 softmax 归一化，\(p(y\mid x)=\prod_tp(y_t\mid x,y_{<t})\)，\(p(y_t\mid\cdot)=e^{f_t}/\sum_ve^{f_t(v)}\)，于是

\[
-\log p(y\mid x)=\sum_t\Bigl(\log\sum_ve^{f_t(v)}-f_t(y_t)\Bigr)=\sum_t\bigl(\log Z_t-f_t(y_t)\bigr).
\]

每个加项正是 Lean 恒等式 [Log.Softmax.eq.Add.LogSumExp](http://www.lemma.cn/lean/?module=Tensor.Log.Softmax.eq.Add.LogSumExp)；乘积变求和这一步，是同一个“马尔可夫乘积的对数是逐步项之和”的性质。两种模型有同一个分子，只差分母：一个 \(Z(x)\) 对一串逐步归一化项的乘积。MEMM [18] 是 CRF 的局部归一化的同类，其 label bias 问题（出边少的状态不管观测如何都把全部质量传下去）对应于序列到序列模型的 exposure bias。Andor 等人 [1] 为全局归一化的神经句法分析器提出了同样的主张。

**从标注到生成，什么变了**

1. **对齐与观测** 标注中 \(|y|=|x|\)，每个位置上 \(x\) 都完全可见；生成中输出长度可变，没有对齐，已生成的前缀 \(y_{<t}\) 是第 \(t\) 步条件的一部分。我们把“序列到序列”一词留给不对齐的自回归情形。
2. **马尔可夫结构被搬了家** 线性链 CRF 对**标签**是一阶的，对 \(x\) 则任意；自回归模型 \(p(y_t\mid x,y_{<t})\) 以**整个前缀**为条件，因此只在扩大的状态 \((x,y_{<t})\) 上才是马尔可夫的。在该状态空间里转移是确定性的（追加所选词元），马尔可夫性是平凡的。
3. **归一化项** 对 \(k^n\) 条路径的 \(Z(x)\) 因一阶依赖可用动态规划在 \(O(nk^2)\) 内算出；对依赖前缀的模型，对 \(V^n\) 条序列的全局和没有这样的递推，所以改为局部归一化。
4. **推断** Viterbi 对链是精确的；贪心、beam 与采样对生成是近似的。
5. **训练** 标注最小化监督的 \(\log Z-\text{score}\)。生成用教师强制的交叉熵训练（需要真实前缀），或用期望奖励训练，策略梯度就是在这里出场的（第 7 节）。

# 9 对比表

## 9.1 各模型中的马尔可夫假设

表 2 比较各个模型分解的是什么、每个因子以什么为条件、如何归一化、Lean 里有什么。每一行里，长度为 \(n\) 的对象的概率都是单步因子的乘积，由此得到：（i）对数中是局部项之和；（ii）线性时间的递推（前向、后向、Viterbi、Bellman、值迭代）；（iii）以对 \(t\) 归纳作为证明技术（CRF 引理对 \(t\) 归纳；MDP 用 [hist_step](http://www.lemma.cn/lean/?module=Random.Integral.eq.Integral_Integral.of.All_LeNorm.StronglyMeasurable.history) 与展开）。

| 模型 | 分解 | 条件于 | 归一化 | Lean |
|---|---|---|---|---|
| HMM | \(p(x,y)=\prod_tp(y_t\mid y_{t-1})\,p(x_t\mid y_t)\)（生成式） | 前一个标签；发射只依赖当前标签 | 局部，\(Z=1\) | `IsHiddenMarkovPr`，`crf.markov`（由条件独立推出） |
| 线性链 CRF | \(p(y\mid x)=\frac1{Z(x)}\prod_t\psi_t(y_{t-1},y_t,x)\)（判别式） | 相邻标签；\(x\) 任意、完全可见 | 全局 \(Z(x)\)，对 \(k^n\) 条路径 | HMM-条件特例：`crf.logits`、\(\log Z-\)score、`crf.viterbi`；离散 HMM 的HMM 恒等式（`hmm_identity`）；一般 \(\psi_t\) 作为模型、归一化边缘与 \(\nabla\log Z\) 未形式化 |
| MEMM | \(\prod_tp(y_t\mid y_{t-1},x)\) | 前一个标签与 \(x\) | 局部，逐步 softmax | 未形式化 |
| MDP / 策略梯度 | \(\iota(s_0)\prod_t\pi_\theta(a_t\mid s_t)T(s_{t+1}\mid s_t,a_t)\) | 下一状态与奖励只依赖 \((s_t,a_t)\)；策略只依赖 \(s_t\) | 局部，\(Z=1\) | 轨迹测度、[joint_succ](http://www.lemma.cn/lean/?module=Random.Map)、[hist_step](http://www.lemma.cn/lean/?module=Random.Integral.eq.Integral_Integral.of.All_LeNorm.StronglyMeasurable.history)、Bellman、策略梯度、优势、GAE |
| PPO（算法） | 同样的轨迹律；目标 \(L^{\rm CLIP}\)，带比值 \(\rho_t\) 与学习得到的 critic | 同 MDP | 局部，\(Z=1\) | **无**：裁剪替代目标、比值、KL、价值裁剪、学习得到的 critic 都未形式化；只有策略梯度之内的（截断）GAE 优势得到论证（精确 \(V\)） |
| 自回归语言模型 | \(\prod_tp(y_t\mid x,y_{<t})\) | 整个前缀 | 局部，逐步 softmax | 未形式化（只有 log-softmax 与两变量链式法则）；作为状态为 \((x,y_{<t})\) 的 MDP，马尔可夫性是平凡的 |

表 2：本文各模型中的马尔可夫假设。HMM 对 CRF 的差别在归一化（局部对全局）以及建模对象（\(p(x,y)\) 对 \(p(y\mid x)\)）；MDP 对 PPO 的差别在种类（模型对算法）。

## 9.2 序列标注对序列到序列生成

表 3 概括第 8 节，是概念性对比；只有标“Lean”的条目是定理，其余都是概念性比较。

| | 序列标注（CRF） | 序列到序列生成（语言模型 / PPO） |
|---|---|---|
| 输入 / 对齐 | 对齐，\(\lvert y\rvert=\lvert x\rvert\)，\(x\) 完全可见 | 不对齐，长度可变；已生成的前缀是条件的一部分 |
| 归一化 | 对 \(k^n\) 条标签序列的全局配分函数 | 局部归一化的词元 softmax |
| 依赖 | 相邻标签（一阶）与整个 \(x\) | 整个前缀 \(y_{<t}\)（以及 \(x\)）；只在状态 \((x,y_{<t})\) 上是马尔可夫的 |
| 训练 | 监督似然，NLL \(=\log Z-\)score（Lean，HMM-条件特例） | 教师强制的交叉熵，或期望奖励（策略梯度 / PPO） |
| 推断 | 精确动态规划：前向、后向、Viterbi（Lean：前向递推；Viterbi 只有数值） | 近似：贪心、beam、采样 |
| 失效模式 | 若局部归一化则 label bias（MEMM）；独立 softmax 会出现非法标签序列 | exposure bias；beam 大小反常 |
| 梯度 | \(\nabla\text{NLL}=\mathbb E_{\rm model}[\text{features}]-\text{empirical}\)（不在 Lean 中） | \(\nabla\mathbb E[R]=\mathbb E[\sum_t\gamma^t\hat A_t\nabla\log\pi_\theta(a_t\mid s_t)]\)（Lean，有限 \(S,A\)，精确 \(V\)）；\(\mathbb E[\nabla\log\pi]=0\)（Lean） |

表 3：序列标注对序列到序列生成。

# 10 形式化工件

**模块与版本** 每条定理都链接到 [math-proof/lemma](https://github.com/math-proof/lemma) [15] 中对应的模块（省略前缀 `Lemma.`）。时序差分引理（`delta_ae_bdd`、`E_delta_psi`、`E_sum_delta`）在轨迹模型的优势文件里；取代对 \(V\) 与 \(\nabla V\) 之假设的界 `V_bdd` 与 `gradV_bdd` 在可微性文件里。项目使用 Lean `v4.33.1` 与 mathlib。

**检查** 所引用的模块中都没有 `sorry`、`admit` 或新增 `axiom`。`#print axioms` 对定理 5.1–5.4 的声明、第 4 节至第 7.2 节的 log-softmax、条件独立、链式法则与零得分引理，以及定理 6.2–7.6 和辅助引理，给出的公理都只有 `propext`、`Classical.choice`、`Quot.sound`。

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
