项目工件：<https://github.com/math-proof/lemma>

Bellman：[V 与 Q](http://www.lemma.cn/lean/?module=Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman)，归纳：[截断形式](http://www.lemma.cn/lean/?module=Tensor.Eq.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient)，极限：[REINFORCE](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.IsFinite.policy_gradient_theorem)

无偏优势估计：[Lean 4](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.unbiased_advantage_estimate)

# 摘要

在 REINFORCE 里把蒙特卡洛回报换成“回报减去状态价值基线”，也就是常说的优势（advantage），通常写成价值函数时序差分误差的折扣和。“这样换不改变梯度”几乎人人都会说，但教科书上的推导对几件事一带而过：在零概率事件上取条件、梯度与无穷级数及期望的交换、无穷级数的裂项相消。

我们用 Lean 4 + mathlib 把这件事完整地机器验证了一遍。模型是折扣马尔可夫决策过程（MDP）：状态、动作空间有限，奖励有界，策略 \(\pi_\theta\) 可微，参数 \(\theta\) 取值于任意实赋范空间；整条轨迹的分布就是 mathlib 里的 Ionescu-Tulcea 测度。取精确的状态价值 \(V_t\)，定义优势

\[
\hat A_t=\sum_{k\ge0}\gamma^k\bigl({\color{red}r}_{t+k}+\gamma V_{t+k+1}({\color{red}s}_{t+k+1})-V_{t+k}({\color{red}s}_{t+k})\bigr),
\]

我们证明了

\[
\sum_{t}{}'\,\gamma^t\,\nabla_\theta\mathbb E_\theta[{\color{red}r}_t]
=\sum_{t}{}'\,\gamma^t\,\mathbb E_\theta\bigl[\hat A_t\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\bigr].
\]

对有限 MDP，策略梯度定理的动作价值（占用测度）形式此前已由 Zhang 在 Lean 4 中形式化 [[25]](https://github.com/ShangtongZhang/rl-theory-in-lean/commit/2a9d01a236961b1c9bc451a8926346364fc66e7f)。我们的形式化建立在轨迹层面：形式化了模型的 Bellman 方程、\(\nabla_\theta V_t\) 的一步递推，并用归纳法把递推展开成带余项 \(\gamma^n\mathbb E[\nabla_\theta V_n({\color{red}s}_n)]\) 的精确截断策略梯度恒等式；再令 \(n\to\infty\)，得到动作价值形式和 REINFORCE（回报加权）形式的策略梯度定理；上面的无偏优势估计是本文的主结果。此外还介绍了一套像教科书一样书写极限的 Lean 记号。所有定理只依赖 `propext`、`Classical.choice`、`Quot.sound` 三条公理。另外我们发现：这些定理陈述里带着的“奖励独立性”假设，其实没有任何证明用到它。

# 1 引言

策略梯度定理 [21] 说的是：参数化策略的期望折扣回报，其梯度等于得分函数 \(\nabla_\theta\log\pi_\theta(a\mid s)\) 乘以动作价值的期望。REINFORCE [24] 则直接用采样回报加权。再减去一个只依赖状态的基线，期望不变而方差可能变小 [24][3]；基线取状态价值函数，就得到优势；而价值函数时序差分残差的折扣和，正是广义优势估计（GAE）里 \(\lambda=1\) 的那一个 [[19]](https://arxiv.org/abs/1506.02438)。教科书 [20] 几行就推完了。

这几行背后其实藏着不少分析上的细节：目标函数是无穷折扣级数，求导要和这个级数、以及对无穷长轨迹的期望交换次序；像 \(\mathbb E[\,\cdot\mid s_t=x]\) 这样的条件期望在到达不了的状态上根本没有定义；而 \(\sum_k\gamma^k(\gamma V(s_{t+k+1})-V(s_{t+k}))\) 的裂项还需要边界项收敛。本文记录的是 `lemma` 库 [[6]](https://github.com/math-proof/lemma) 里基于 mathlib [22][[17]](https://leanprover-community.github.io/mathlib4_docs/) 的一套 Lean 4 [2] 形式化，上面每一步都被检查过。

**贡献。** 对有限 MDP，策略梯度定理的动作价值形式此前已由 Zhang 在 Lean 4 中形式化 [[25]](https://github.com/ShangtongZhang/rl-theory-in-lean/commit/2a9d01a236961b1c9bc451a8926346364fc66e7f)，两者的比较见第 2 节。在此基础之外，本文的贡献是下面四项。每条 Lean 陈述都以模块路径命名，点开就是交互页面。

1. **无偏优势估计**（第 8 节，主结果）：用价值函数时序差分残差的折扣和给得分函数加权，策略梯度不变：[Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.unbiased_advantage_estimate](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.unbiased_advantage_estimate) [[14]](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.unbiased_advantage_estimate)。
2. **REINFORCE 形式**（第 7.4 节）：用回报给得分函数加权的策略梯度定理 [Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.IsFinite.policy_gradient_theorem](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.IsFinite.policy_gradient_theorem) [[11]](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.IsFinite.policy_gradient_theorem)；途中也得到动作价值形式 [Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.IsFinite.Q_Function](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.IsFinite.Q_Function) [[10]](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.IsFinite.Q_Function)。
3. **归纳法证明**（第 7 节）：\(\nabla_\theta V_t\) 的一步递推 [Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.recursion](http://www.lemma.cn/lean/?module=Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.recursion) [[16]](http://www.lemma.cn/lean/?module=Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.recursion)，用归纳法展开 [Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.induct](http://www.lemma.cn/lean/?module=Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.induct) [[15]](http://www.lemma.cn/lean/?module=Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.induct)，得到带余项 \(\gamma^n\mathbb E[\nabla_\theta V_n({\color{red}s}_n)]\) 的精确截断恒等式 [Tensor.Eq.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient](http://www.lemma.cn/lean/?module=Tensor.Eq.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient) [[13]](http://www.lemma.cn/lean/?module=Tensor.Eq.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient)，再令 \(n\to\infty\) 取极限。据我们所知，这是第一个沿教科书推导路线、以归纳法严格化的策略梯度定理 Lean 4 证明（见第 2 节）。
4. **轨迹层面的模型**（第 5、6 节）：有限 \(S\)、\(A\) 的折扣 MDP，参数化策略的参数取值于任意实赋范空间；轨迹的分布是 mathlib 的 Ionescu-Tulcea 测度 `Kernel.trajMeasure`，\(V_t\)、\(Q_t\) 定义为条件期望，Bellman 方程是 [Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman](http://www.lemma.cn/lean/?module=Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman) [[9]](http://www.lemma.cn/lean/?module=Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman)。

第 3、4 节介绍这些陈述所用的记号：库里像教科书一样的极限写法 \(\lim [n\to\infty]\,e=a\)（例子是 [Real.Eq_0.Lim.of.LtAbs.IsFinite](http://www.lemma.cn/lean/?module=Real.Eq_0.Lim.of.LtAbs.IsFinite) [[8]](http://www.lemma.cn/lean/?module=Real.Eq_0.Lim.of.LtAbs.IsFinite)），以及 \(\mathbb E\) / \(\mathbb P\) 的绑定式写法和渲染器的配色。

# 2 相关工作

策略梯度定理出自 Sutton 等人 [21]；似然比估计和强化基线可以追溯到 Williams [24]。Greensmith、Bartlett、Baxter [3] 把基线当作方差缩减手段做了系统分析；Schulman 等人 [[19]](https://arxiv.org/abs/1506.02438) 提出 GAE，本文研究的优势就是其 \(\lambda=1\) 的情形。有限 MDP 的标准参考书是 Puterman [18] 和 Sutton、Barto [20]。

**形式化方面。** CertRL [23] 在 Coq 里证明了值迭代与策略迭代的收敛；Chevallier 与 Fleuriot [[1]](https://arxiv.org/abs/2112.05996) 在 Isabelle/HOL 里形式化了带奖励的有限 MDP，包括 Bellman 方程、\(\gamma<1\) 时最优策略的存在性，以及值迭代与策略迭代。两者都没有涉及策略梯度。在 Lean 4 里，TorchLean [[5]](https://github.com/lean-dojo/TorchLean) 证明了关于 MDP 与 Bellman 算子的结构性和动态规划性质，并包含策略梯度和 PPO 的训练代码，但没有策略梯度定理。

与本文最接近的是 Zhang 的 `rl-theory-in-lean` 中的 `PolicyGradient` 模块 [[25]](https://github.com/ShangtongZhang/rl-theory-in-lean/commit/2a9d01a236961b1c9bc451a8926346364fc66e7f)。这是一套实验性的、主要由机器生成的开发（其提交与 AI 助手共同署名），2026 年 3 月提交，后来从该项目的 main 分支撤回，在所引用的提交处仍可访问。对有限的状态和动作空间、带有限个实参数的策略，它在 Lean 4 中证明了占用测度形式的折扣策略梯度定理

\[
\nabla_\theta J(\theta)=(1-\gamma)^{-1}\sum_{s,a}d^{\pi_\theta}(s)\,\pi_\theta(a\mid s)\,Q^{\pi_\theta}(s,a)\,\nabla_\theta\log\pi_\theta(a\mid s),
\]

同时还证明了价值函数梯度的递推、对数导数技巧、Fisher 信息矩阵以及自然策略梯度。那套形式化把价值函数定义为 Bellman 算子的不动点（Banach 不动点定理），由 \(V=(I-\gamma P_\theta)^{-1}r_\theta\) 得到它的可微性，用线性代数解出梯度递推，再把解展开成 Neumann 级数，并借助折扣状态占用测度 \(d^{\pi_\theta}\) 重新整理；它要求策略严格为正，其中没有轨迹、回报或优势。我们的则建立在轨迹层面：轨迹的分布是 mathlib [[17]](https://leanprover-community.github.io/mathlib4_docs/) 的 `Kernel.trajMeasure`，也就是 Ionescu-Tulcea 定理 [4] 的实现；价值函数是条件期望；参数取值于任意实赋范空间；在动作价值形式之外，我们还证明了 REINFORCE 形式，主结果则是无偏优势估计。据我们所知（基于 GitHub、arXiv 和网页检索），这是第一个沿教科书纸笔推导路线、以数学归纳法完成的策略梯度定理 Lean 4 证明：教科书 [20]（§13.2）对一步递推“反复展开”并以省略号带过，我们将其严格化为对展开步数 \(n\) 的数学归纳法，在轨迹测度上得到带显式余项 \(\gamma^n\mathbb E[\nabla_\theta V_n({\color{red}s}_n)]\) 的精确有限步恒等式，再令 \(n\to\infty\) 取极限得到无穷时域的定理；我们所知的另一个形式化证明 [[25]](https://github.com/ShangtongZhang/rl-theory-in-lean/commit/2a9d01a236961b1c9bc451a8926346364fc66e7f) 则走不动点与 Neumann 级数的路线，没有采用归纳法。两个证明只共享教科书上的出发点，即 Sutton 等人 [21] 的一步梯度递推和对数导数技巧；除此之外，它们的定义、证明路线和最终陈述都不相同，我们的证明是独立完成的。

# 3 教科书式的极限记号

mathlib 用滤子（filter）表达收敛：`Filter.Tendsto f atTop (𝓝 a)`；要给极限取一个值，则用 `Filter.limUnder`。它没有一种读起来像教科书上 \(\lim_{n\to\infty}e=a\) 的写法。库里为此补了一组宏，本文用到的是下面两种：

```
lim [n → ∞] e = a   ⟹   Filter.Tendsto (fun n => e) Filter.atTop (nhds a)
lim [n → ∞] e       ⟹   Filter.limUnder Filter.atTop (fun n => e)
```

同一套写法还覆盖 \(n\to-\infty\)（`atBot`）、趋于一点 \(x\to x_0\)（去心邻域滤子）以及单侧极限 \(x\to x_0^{+}\)、\(x\to x_0^{-}\)；约束变量的类型也可以显式写出，如 `lim [(n : ℕ) → ∞] e = a`。库里另外还定义了箭头 `x → ∞` 与 `x → 0`，用于带无穷小的有序域，分别表示 \(x\) 是无穷大、无穷小（借助 `ArchimedeanClass.mk`），本文用不到。反方向上，有一个 unexpander 会把 `Filter.Tendsto (fun n => e) atTop (nhds a)` 在 Lean infoview 里重新打印成 `lim [n → ∞] e = a`，lemma.cn 的渲染器则把它排成 \(\lim_{n\to\infty}e=a\)。

有两点值得强调。

1. **纯语法。** 这套记号只由宏和打印用的 unexpander 组成，展开之后什么都不剩：第 9 节的元程序在本文所有定理的依赖图里，没有找到这个记号模块中的**任何**常量。它不给可信基增加任何东西。
2. **等式形式表示收敛。** 等式形式是整体解析的，优先级高于光秃形式，所以 `lim [n → ∞] e = a` 断言的是“数列收敛到 \(a\)”。它不是等式 \(\mathtt{limUnder}\,(\ldots)=a\)：`limUnder` 通过选择来定义，数列发散时返回一个不确定的值，于是这种等式对发散数列也可能成立。因此本文始终使用等式形式。

**引理 3.1（[Real.Eq_0.Lim.of.LtAbs.IsFinite](http://www.lemma.cn/lean/?module=Real.Eq_0.Lim.of.LtAbs.IsFinite) [[8]](http://www.lemma.cn/lean/?module=Real.Eq_0.Lim.of.LtAbs.IsFinite)）。** 设 \(\gamma\in\mathbb R\)，\(x:\mathbb N\to\mathbb R\)，\(|\gamma|<1\) 且 \(\{|x_n|:n\in\mathbb N\}\) 有上界。则

\[
\lim_{n\to\infty}\gamma^n x_n=0.
\]

Lean 里的结论写作 `lim [n → ∞] γ ^ n * x n = 0`，展开后就是 `Filter.Tendsto (fun n => γ ^ n * x n) atTop (nhds 0)`。证明按 \(\gamma\) 的符号分情况；当 \(0<\gamma<1\) 时，用 mathlib 的 `tendsto_pow_atTop_nhds_zero_of_lt_one` 和 `squeeze_zero_norm` 夹逼 \(|\gamma^nx_n|\le\gamma^nM\)。引理 3.1 下面用到两次：截断策略梯度的余项（7.4 节），以及裂项和的边界项（第 8 节）。

# 4 期望与概率记号

## 4.1 绑定式语法

库里为概率空间 \((\Omega,\pi)\) 上的随机变量 \(x:\Omega\to\alpha\) 定义了一套绑定式写法：方括号里写“对谁积分”，圆括号里写被积式，后面可以跟 `|` 加条件。

| Lean 写法 | 含义 |
|---|---|
| `𝔼[x: π](f x)` | 标量 \(\mathbb E_\pi[f({\color{red}x})]\) |
| `𝔼[x: π](f x \| y = y0)` | 标量，在观测 \({\color{red}y}=y_0\) 下取条件 |
| `𝔼[x: π](f x \| y)` | 关于 \(y\) 随机：\(\omega\mapsto\mathbb E_\pi[f({\color{red}x})\mid{\color{red}y}=y(\omega)]\) |
| `𝔼[x: π \| y]((x + y)^2)` | 积掉 \(x\)，保留 \(y\)：一个关于 \({\color{magenta}y}\) 的随机变量 |

方括号里写多个变量（如 `𝔼[x, z: π](…)`）表示对它们的联合分布积分；除非独立，这和逐个求边缘期望不是一回事。概率的写法同理：`ℙ[π](x = x0)` 是 \({\color{red}x}\) 取值 \(x_0\) 的概率；`ℙ[π](x = x0 | y = y0)` 是固定观测下的条件概率；`ℙ[π](x = x0 | y)` 是随机量 \(\omega\mapsto\mathbb P({\color{red}x}=x_0\mid{\color{red}y}=y(\omega))\)；光秃秃的 `ℙ[π](x)` 则是密度在随机点 \(x(\omega)\) 处的取值。这里的 `=` 读作“在……处取值”，`∧` 把几个值打包成联合点，`|` 表示条件。

## 4.2 颜色约定

lemma.cn 的渲染器会把每条 Lean 定理排成 LaTeX，并按概率角色给标识符上色。从渲染器源码里读出来的规则是：

- **红色：随机变量。** 声明为从某个概率测度（带 `IsProbabilityMeasure` 或库里的 `PSpace` 实例）的样本空间出发的函数 \(\Omega\to\alpha\) 的变量；\(\mathbb E\) 方括号里被积掉的变量；\(\mathbb P\) 事件里 `=` 左边的变量。
- **品红：随机自变量（random argument）。** 作为函数自变量出现、使整个表达式本身变成随机量的随机变量：\(\mathbb E\) 方括号里 `|` 后面保留的自由变量、\(\mathbb E(\ldots\mid y)\) 里的条件列表、\(\mathbb P(x)\) 或 \(\mathbb P(x\mid y)\) 里的光秃因子。
- **黑色：观测值。** 普通的确定性项，比如观测里固定的 \(x_0,y_0\)。

所以 \(\mathbb E[{\color{red}y}\mid{\color{red}x}=x]\) 是一个数，而 \(\mathbb E[{\color{red}y}\mid{\color{magenta}x}]\) 是把 \({\color{red}x}(\omega)\) 代入它得到的随机变量。本文沿用同样的配色：\({\color{red}s}_t,{\color{red}a}_t,{\color{red}r}_t\) 是红色，\(x,u,y\) 是黑色的具体状态和动作，而 \(V_t({\color{magenta}s}_t)\) 用品红自变量表示“沿轨迹取值的状态函数”。

## 4.3 策略梯度定理中实际使用的写法

第 6 到第 8 节的定理并没有用上面的绑定式语法，而是直接用 mathlib 的 Bochner 积分和条件测度：\(\mathbb E_\theta[f]\) 就是 `∫ ω, f ω ∂M.traj θ`，\(\mathbb E_\theta[f\mid B]\) 是对 `(M.traj θ)[|B]` 积分，mathlib 里 \(\mu[|B]=\mu(B)^{-1}\,\mu|_B\)。当 \(\mu(B)=0\) 时这是零测度，所以在到达不了的状态上条件期望等于 \(0\)；这也是为什么下面好几条假设只要求在**可达**的 \((t,x)\) 上成立，即 \(\mathbb P_\theta({\color{red}s}_t=x)\neq0\)。另外提醒一句：Lean 的 `tsum`（记作 \(\sum{}'\)）对可和族是它的和，对不可和族定义为 \(0\)。

# 5 MDP 模型

**定义 5.1（模型）。** 设 \(S\)、\(A\) 是带离散 \(\sigma\)-代数的有限类型，\(\Theta\) 是实赋范空间。**策略**是函数 \(\pi:\Theta\to S\to A\to\mathbb R\)，记作 \(\pi_\theta(u\mid x)\)，满足 \(\pi_\theta(u\mid x)\ge0\)、\(\sum_u\pi_\theta(u\mid x)=1\)。**环境**包括：\(S\) 上的初始概率测度 \(\iota\)；从 \(S\times A\) 到 \(S\) 的马尔可夫核 \(T\)；从 \(S\times A\) 到 \(\mathbb R\) 的马尔可夫核 \(R\)（奖励分布）；以及界 \(R_{\max}\)，使得对所有 \((x,u)\) 有 \(R(x,u)\bigl(\mathbb R\setminus[-R_{\max},R_{\max}]\bigr)=0\)。模型 \(M\) 就是环境加策略。

一条轨迹是阶段序列 \(\omega\in(S\times A\times\mathbb R)^{\mathbb N}\)，坐标记为 \({\color{red}s}_t(\omega)\)、\({\color{red}a}_t(\omega)\)、\({\color{red}r}_t(\omega)\)。从状态 \(x\) 出发走一步由核 \(\kappa_\theta(x)=\delta_x\otimes\bigl(\pi_\theta(\cdot\mid x)\otimes R\bigr)\) 给出：动作从策略里采，奖励从 \(R(x,\cdot)\) 里采。阶段链的转移核是 \(K_\theta(x,u,\rho)=(\kappa_\theta\circ T)(x,u)\)（与奖励 \(\rho\) 无关），第一阶段的分布是 \(\mu_0=\kappa_\theta\circ\iota\)。

**定义 5.2（轨迹测度）。** \(\mathbb P_\theta=\mathtt{Kernel.trajMeasure}\;\mu_0\;(K_\theta)_n\)，定义在 \((S\times A\times\mathbb R)^{\mathbb N}\) 上，其中第 \(n\) 个核只看历史的最后一个阶段。

这就是阶段链的 Ionescu-Tulcea 扩张 [4]，由 mathlib [[17]](https://leanprover-community.github.io/mathlib4_docs/) 提供，是一个概率测度。时间齐次性和马尔可夫性都是构造出来的：除了这些核，关于轨迹没有任何额外假设。

**定义 5.3（价值函数）。** 对 \(\gamma\in\mathbb R\)、\(t\in\mathbb N\)、\(x\in S\)、\(u\in A\)，

\[
V_t^\theta(x)=\sum_{k}{}'\,\gamma^k\,\mathbb E_\theta[{\color{red}r}_{t+k}\mid{\color{red}s}_t=x],\qquad
Q_t^\theta(x,u)=\sum_{k}{}'\,\gamma^k\,\mathbb E_\theta[{\color{red}r}_{t+k}\mid{\color{red}s}_t=x,{\color{red}a}_t=u].
\]

从 \(t\) 开始的折扣回报是 \(G_t=\sum_k{}'\,\gamma^k{\color{red}r}_{t+k}\)。

模型文件里还证明了：在可达状态上 \(V_t^\theta(x)\) 等于一个与时间无关的闭式 \(V^\theta_c(x)\)；\(|Q_t^\theta|\le(1-\gamma)^{-1}|R_{\max}|\)；并且几乎处处 \(G_t\) 是收敛级数、满足同样的界。目标函数是 \(J(\theta)=\sum_t{}'\,\gamma^t\mathbb E_\theta[{\color{red}r}_t]\)。模型引理 `obj_hasFDerivAt` 说明：当 \(\gamma\in[0,1)\)、策略可微且梯度一致有界时，\(J\) 是 Fréchet 可微的，并且

\[
\nabla_\theta J(\theta)=\sum_t{}'\,\gamma^t\,\nabla_\theta\mathbb E_\theta[{\color{red}r}_t].\tag{1}
\]

下面所有策略梯度定理的左边都是 (1) 的右边。

**常用假设。** 为了简洁，记：

- (D) \(\gamma\in[0,1)\)；
- (P1) 对每个 \(x,u\)，\(\theta\mapsto\pi_\theta(u\mid x)\) 可微；
- (P2) \(\sup_{\theta,x,u}\|\nabla_\theta\pi_\theta(u\mid x)\|<\infty\)；
- (I) 对每个 \(t\)，在 \(\mathbb P_\theta\) 下 \({\color{red}r}_t\) 与历史 \(({\color{red}s}_i,{\color{red}a}_i)_{i<t}\) 独立。

(I) 出现在定理陈述里；第 9 节会说明证明并没有用到它。

# 6 Bellman 方程

**定理 6.1（Bellman 方程 [[9]](http://www.lemma.cn/lean/?module=Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman)）。** 设 (I) 在时刻 \(t\) 成立且 (D) 成立，记 \(V_t=V_t^\theta\)、\(Q_t=Q_t^\theta\)。则对所有 \(x\in S\)、\(u\in A\)：

\[
\begin{aligned}
V_t(x)&=\mathbb E_\theta\bigl[Q_t(x,{\color{red}a}_t)\bigm|{\color{red}s}_t=x\bigr],\\
V_t(x)&=\mathbb E_\theta\bigl[{\color{red}r}_t+\gamma\,V_{t+1}({\color{magenta}s}_{t+1})\bigm|{\color{red}s}_t=x\bigr],\\
Q_t(x,u)&=\mathbb E_\theta\bigl[{\color{red}r}_t+\gamma\,V_{t+1}({\color{magenta}s}_{t+1})\bigm|{\color{red}s}_t=x,\ {\color{red}a}_t=u\bigr].
\end{aligned}
\]

三个等式分别由 [Tensor.EqExpect.of.Eq_Expect.V_Function](http://www.lemma.cn/lean/?module=Tensor.EqExpect.of.Eq_Expect.V_Function)（\(Q_t\) 的策略平均）、[Tensor.EqExpect.of.Eq_Conditioned.Bellman.V_Function](http://www.lemma.cn/lean/?module=Tensor.EqExpect.of.Eq_Conditioned.Bellman.V_Function) 和 [Tensor.EqExpect.of.Eq_Conditioned.Bellman.Q_Function](http://www.lemma.cn/lean/?module=Tensor.EqExpect.of.Eq_Conditioned.Bellman.Q_Function) 组装而成。条件事件为零测时两边都是 \(0\)。第一个引理只需要 (D)；后两个引理的文档注释里就写明，对马尔可夫模型而言独立性假设是多余的，在 Lean 里它是一个以下划线开头、未被使用的参数。若 \(\gamma=1\)，Lean 中不可和级数的 `tsum` 为 \(0\)，第一个等式就不成立了，所以 (D) 是必须的。

# 7 归纳法证明策略梯度定理

库里通向策略梯度定理的路线是：先对 Bellman 方程求一次导，再对视野长度做归纳把结果展开，然后对初始状态积分，最后让视野趋于无穷。

## 7.1 一步递推

**定理 7.1（递推 [[16]](http://www.lemma.cn/lean/?module=Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.recursion)）。** 设 (I) 在时刻 \(t\) 成立，(D)、(P1)、(P2) 成立，\(x\) 在时刻 \(t\) 可达。则

\[
\nabla_\theta V_t(x)=\sum_{u}Q_t(x,u)\,\nabla_\theta\pi_\theta(u\mid x)
+\gamma\sum_{y}\mathbb P_\theta({\color{red}s}_{t+1}=y\mid{\color{red}s}_t=x)\,\nabla_\theta V_{t+1}(y),
\]

其中 \(\nabla_\theta V_t(x)\) 是 \(\theta\mapsto V^\theta_t(x)\) 的 Fréchet 导数，\(Q\)、\(V\) 看作 \(\theta\) 的函数。

证明先把 \(V_t\) 改写成闭式，再用模型引理 `grad_V_rec`（即定理 6.1 中 Bellman 方程的导数），最后把条件转移概率认出来就是核 \(\sum_u\pi_\theta(u\mid x)T(x,u,y)\)。

## 7.2 归纳展开

**定理 7.2（展开的递推 [[15]](http://www.lemma.cn/lean/?module=Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.induct)）。** 设 (I) 对每个 \(t\) 成立，(D)、(P1)、(P2) 成立，\(x\) 在时刻 \(0\) 可达。则对每个 \(n\in\mathbb N\)，

\[
\nabla_\theta V_0(x)=\sum_{t<n}\gamma^t\sum_y\mathbb P_\theta({\color{red}s}_t=y\mid{\color{red}s}_0=x)\sum_u Q_t(y,u)\,\nabla_\theta\pi_\theta(u\mid y)
+\gamma^n\sum_y\mathbb P_\theta({\color{red}s}_n=y\mid{\color{red}s}_0=x)\,\nabla_\theta V_n(y).
\]

证明思路：先把条件概率换成 \(t\) 步核 \(P^t_\theta(x,y)\)，然后对 \(n\) 归纳。\(n=0\) 平凡。从 \(n\) 到 \(n+1\)：在每个 \(P^n_\theta(x,y)\neq0\) 的 \(y\) 上（这样的 \(y\) 在时刻 \(n\) 可达）用定理 7.1 展开余项 \(\gamma^n\sum_yP^n_\theta(x,y)\nabla_\theta V_n(y)\)，得到的二重和再用 Chapman–Kolmogorov 恒等式 \(P^{n+1}_\theta(x,z)=\sum_yP^n_\theta(x,y)P^1_\theta(y,z)\) 合并。

## 7.3 截断恒等式

**定理 7.3（截断策略梯度 [[13]](http://www.lemma.cn/lean/?module=Tensor.Eq.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient)）。** 设 (I) 对每个 \(t\) 成立，(D)、(P1)、(P2) 成立。则对每个 \(n\in\mathbb N\)，

\[
\sum_t{}'\,\gamma^t\nabla_\theta\mathbb E_\theta[{\color{red}r}_t]
=\mathbb E_\theta\Bigl[\sum_{t<n}\gamma^tQ_t({\color{magenta}s}_t,{\color{magenta}a}_t)\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\Bigr]
+\gamma^n\,\mathbb E_\theta\bigl[\nabla_\theta V_n({\color{magenta}s}_n)\bigr].
\]

证明思路：由模型引理 `grad_obj`，左边等于 \(\sum_x\iota(x)\,\nabla_\theta V_c^\theta(x)\)；对每个 \(\iota(x)\neq0\) 的 \(x\) 用定理 7.2 展开 \(\nabla_\theta V_0(x)\)。右边用引理 `E_score` 计算

\[
\mathbb E_\theta[g({\color{red}s}_t,{\color{red}a}_t)\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)]=\sum_y\mathbb P_\theta({\color{red}s}_t=y)\sum_ug(y,u)\nabla_\theta\pi_\theta(u\mid y),
\]

这其实就是对数导数技巧 \(\pi\,\nabla\log\pi=\nabla\pi\) 对 \(({\color{red}s}_t,{\color{red}a}_t)\) 的分布求和；状态边缘分布为 \(\mathbb P_\theta({\color{red}s}_t=y)=\sum_x\iota(x)P^t_\theta(x,y)\)。于是两边都化成相等的有限和。

注意：虽然出现了 \(t<n\) 的有限和，定理 7.3 讨论的仍然是折扣无穷视野的目标函数——它对每个截断层级都精确成立，并带有显式余项。它不是关于有限视野 MDP 的定理。

## 7.4 取极限

在定理 7.3 中令 \(n\to\infty\)，就得到策略梯度定理：先是动作价值形式，再是 REINFORCE 形式。

**定理 7.4（策略梯度，动作价值形式 [[10]](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.IsFinite.Q_Function)）。** 设 (I) 对每个 \(t\) 成立，(D)、(P1)、(P2) 成立，并且

- (B\(_{\nabla V}\)) \(\sup\{\|\nabla_\theta V_t(x)\| : \mathbb P_\theta({\color{red}s}_t=x)\neq0\}<\infty\)。

则

\[
\sum_t{}'\,\gamma^t\nabla_\theta\mathbb E_\theta[{\color{red}r}_t]=\sum_t{}'\,\gamma^t\,\mathbb E_\theta\bigl[Q_t({\color{magenta}s}_t,{\color{magenta}a}_t)\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\bigr].
\]

证明思路：只有可达状态带质量，所以余项满足 \(\|\mathbb E_\theta[\nabla_\theta V_n({\color{red}s}_n)]\|\le\max(B,0)\)，于是由引理 3.1 得 \(\lim_{n\to\infty}\gamma^n\|\mathbb E_\theta[\nabla_\theta V_n({\color{red}s}_n)]\|=0\)，再用 `tendsto_zero_iff_norm_tendsto_zero` 化为 \(\lim_{n\to\infty}\gamma^n\mathbb E_\theta[\nabla_\theta V_n({\color{red}s}_n)]=0\)。右边级数每一项不超过 \(\gamma^t\,|A|\,(1-\gamma)^{-1}|R_{\max}|\max(C,0)\)（\(C\) 是 (P2) 的界），因此可和。交换积分与有限和；右边级数的部分和收敛到它的 `tsum`（`HasSum.tendsto_sum_nat`），两个极限由极限唯一性（`tendsto_nhds_unique`）相等。

**引理 7.5（塔性质 [[12]](http://www.lemma.cn/lean/?module=Tensor.Eq.Expect.Grad.Log.Pr.of.Eq_Conditioned.Q_Function.discounted)）。** 在时刻 \(t\) 的 (I) 与 (D) 下，

\[
\mathbb E_\theta\bigl[G_t\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\bigr]=\mathbb E_\theta\bigl[Q_t({\color{magenta}s}_t,{\color{magenta}a}_t)\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\bigr].
\]

**定理 7.6（策略梯度，REINFORCE 形式 [[11]](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.IsFinite.policy_gradient_theorem)）。** 设 (I) 对每个 \(t\) 成立，(D)、(P1)、(P2) 成立，且 \(\bigl\|\sum_k{}'\,\gamma^k\nabla_\theta\mathbb E_\theta[{\color{red}r}_{t+k}\mid{\color{red}s}_t=x]\bigr\|\) 在可达的 \((t,x)\) 上有界。则

\[
\sum_t{}'\,\gamma^t\nabla_\theta\mathbb E_\theta[{\color{red}r}_t]=\sum_t{}'\,\gamma^t\,\mathbb E_\theta\bigl[G_t\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\bigr].
\]

模型引理 `sum_grad_cond` 在可达状态上交换 \(\nabla_\theta\) 与级数，把这个界化成 (B\(_{\nabla V}\))；再逐项用定理 7.4 和引理 7.5 即得。

**极限是如何处理的。** 全程无穷和都是 Lean 的 `tsum`，每个极限都是明确的 `Filter.Tendsto` 命题（方便时用第 3 节的记号书写）。目标函数和回报都是 `tsum`，其可和性来自几何级数控制（`summable_geometric_of_lt_one`、`Summable.of_norm_bounded`、`Summable.mul_right`；回报还用到 `hasSum_geometric_of_lt_one`）。梯度与折扣级数的交换由 mathlib 的 `hasFDerivAt_tsum` 完成，由此得到 (1) 以及 \(V_c^\theta\) 的同类结论。从部分和到 `tsum` 用的是 `HasSum.tendsto_sum_nat` 加 `tendsto_nhds_unique`。整个证明没有引用控制收敛定理，也没有交换积分与级数：关于 \(({\color{red}s}_t,{\color{red}a}_t)\) 的函数的期望都化成了 \(S\times A\) 上的有限和（模型引理 `E_score`、`E_s1`），状态与动作空间有限正是在这里用上的。

# 8 主结果：优势估计的无偏性

**定理 8.1（无偏优势估计 [[14]](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.unbiased_advantage_estimate)）。** 设 \(V:\Theta\to\mathbb N\to S\to\mathbb R\) 对所有 \(\theta,t,x\) 满足 \(V^\theta_t(x)=\sum_k{}'\,\gamma^k\mathbb E_\theta[{\color{red}r}_{t+k}\mid{\color{red}s}_t=x]\)。设 (I) 对每个 \(t\) 成立，(D)、(P1)、(P2) 成立，并且

- (B\(_{\nabla V}\)) \(\sup\{\|\nabla_\theta V_t(x)\| : \mathbb P_\theta({\color{red}s}_t=x)\neq0\}<\infty\)；
- (B\(_V\)) \(\sup\{|V^\theta_t(x)| : \mathbb P_\theta({\color{red}s}_t=x)\neq0\}<\infty\)。

定义优势

\[
\hat A_t=\sum_k{}'\,\gamma^k\bigl({\color{red}r}_{t+k}+\gamma\,V^\theta_{t+k+1}({\color{magenta}s}_{t+k+1})-V^\theta_{t+k}({\color{magenta}s}_{t+k})\bigr).
\]

则

\[
\sum_t{}'\,\gamma^t\nabla_\theta\mathbb E_\theta[{\color{red}r}_t]=\sum_t{}'\,\gamma^t\,\mathbb E_\theta\bigl[\hat A_t\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\bigr].
\]

由 (1)，左边就是 \(\nabla_\theta J(\theta)\)。\(\hat A_t\) 的每一项是 \(\gamma^k\delta_{t+k}\)，其中 \(\delta_j={\color{red}r}_j+\gamma V_{j+1}({\color{red}s}_{j+1})-V_j({\color{red}s}_j)\) 是时序差分残差，所以 \(\hat A_t\) 就是用精确价值函数算出的 \(\lambda=1\) 的 GAE [[19]](https://arxiv.org/abs/1506.02438)。

**证明。**

*第一步：化归到 REINFORCE。* 借助 `sum_grad_cond`，把 (B\(_{\nabla V}\)) 改写成定理 7.6 所需的界，左边就变成

\[
\sum_t{}'\,\gamma^t\,\mathbb E_\theta\bigl[G_t\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\bigr].
\]

剩下只需对每个 \(t\) 证明

\[
\mathbb E_\theta\bigl[\hat A_t\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\bigr]=\mathbb E_\theta\bigl[G_t\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)\bigr].
\]

*第二步：几乎处处裂项。* 几乎处处，级数 \(\sum_k\gamma^k{\color{red}r}_{t+k}\) 收敛到 \(G_t\)（模型引理 `G_hasSum`），并且经过的每个状态都可达（`reach_ae`），于是由 (B\(_V\)) 对所有 \(k\) 有 \(|V_k({\color{red}s}_k(\omega))|\le B\)。令 \(b_k=\gamma^kV_{t+k}({\color{red}s}_{t+k}(\omega))\)，则 \(\gamma^k\delta_{t+k}=\gamma^k{\color{red}r}_{t+k}+(b_{k+1}-b_k)\)；由 \(|b_{k+1}-b_k|\le2B\gamma^k\) 知差分可和，又由引理 3.1 知 \(\lim_{k\to\infty}b_k=0\)，故 \(\sum_k(b_{k+1}-b_k)=-b_0\)，从而

\[
\hat A_t=G_t-V_t({\color{magenta}s}_t)\qquad\mathbb P_\theta\text{-几乎处处}.
\]

*第三步：基线项为零。* 由积分的线性（两个被积函数都可积），\(\mathbb E_\theta[\hat A_t\,\nabla_\theta\log\pi_\theta]=\mathbb E_\theta[G_t\,\nabla_\theta\log\pi_\theta]-\mathbb E_\theta[V_t({\color{red}s}_t)\,\nabla_\theta\log\pi_\theta]\)。模型引理 `E_h_score` 说：对任意 \(h:S\to\mathbb R\)，\(\mathbb E_\theta[h({\color{red}s}_t)\,\nabla_\theta\log\pi_\theta({\color{red}a}_t\mid{\color{red}s}_t)]=0\)。它依赖于得分零均值恒等式 \(\sum_u\pi_\theta(u\mid x)\,\nabla_\theta\log\pi_\theta(u\mid x)=0\)（`score_zero`）；在 Lean 里这条不需要 \(\pi\) 为正，因为 \(\pi_\theta(u\mid x)=0\) 的项自然消失。带正性假设的条件版本是 [Random.Expect_ConditionedGrad_LogProb.eq.Zero.policy](http://www.lemma.cn/lean/?module=Random.Expect_ConditionedGrad_LogProb.eq.Zero.policy) [[7]](http://www.lemma.cn/lean/?module=Random.Expect_ConditionedGrad_LogProb.eq.Zero.policy)。证毕。

**注 8.2。** 第二、三步只用到“\(V\) 是 \((t,x)\) 的函数、且在可达状态上有界”；\(V\) 的定义式只在第一步以及 (B\(_{\nabla V}\)) 中用到。这提示：把精确价值函数换成任意有界的 critic，同样的恒等式应当仍然成立。不过 Lean 里的陈述并没有声称这一点。

# 9 形式化工件

**模块。** 上文每条定理都链接到 [[6]](https://github.com/math-proof/lemma) 仓库提交 `c7c71c4` 中对应的模块（省略前缀 `Lemma.`）。模型本身、它的马尔可夫链引理和可微性引理在另外三个文件中，位于命名空间 `PolicyGradient` 下。

**检查。** 项目使用 Lean `v4.33.1` 与 mathlib。主模块 `lake build` 无错误通过，主模块及其导入的所有本地模块中都没有 `sorry`、`admit` 或新增 `axiom`。在仓库之外的临时文件里运行 `#print axioms`，定理 6.1、7.1、7.2、7.3、7.4、7.6、8.1，引理 7.5，以及三个 Bellman 组成引理，依赖的公理都只有 `propext`、`Classical.choice`、`Quot.sound`。我们还在同一个临时文件里用一段元程序遍历了定理 7.1、7.2、7.3、7.4、7.6、8.1 的依赖图：第 3 节的记号模块虽然被导入，但它的 94 个声明没有一个出现在其中。

**独立性假设没有被用到。** 在通向定理 8.1 的链条里，假设 (I) 原封不动地一路往下传，最终只被定理 7.1 和引理 7.5 接收；而在这两处，参数名都是 `_h₀`。我们在同一个临时文件里又写了一段元程序，打开这两个引理的证明项，确认 (I) 对应的约束变量在证明体中根本没有出现。因此整条链——包括定理 8.1——删去 (I) 之后依然成立；现在的陈述只是多带了一个冗余假设。

# 10 讨论与局限

**奖励独立性假设。** 字面上看，(I) 很强：MDP 中奖励 \({\color{red}r}_t\) 依赖 \(({\color{red}s}_t,{\color{red}a}_t)\)，而后者与更早的状态、动作相关，所以对大多数奖励核来说 (I) 并不成立。但如第 9 节所示，没有任何证明用到它。它留在陈述里只是早期写猜想时的遗留，把它从签名里删掉是最直接的清理工作。

**正则性假设。** (P2) 要求梯度界对 \(\theta\)、\(x\)、\(u\) 一致。比如特征有界的 softmax 策略就满足它，因为此时 \(\nabla_\theta\pi_\theta(u\mid x)=\pi_\theta(u\mid x)\bigl(\phi(x,u)-\sum_{u'}\pi_\theta(u'\mid x)\phi(x,u')\bigr)\)；但梯度随 \(\theta\) 增长的策略就被排除了。(B\(_{\nabla V}\)) 是对导出量的假设，我们预期在 \(\gamma<1\) 时它可以由 (P2) 和奖励界推出；(B\(_V\)) 也应能由 \(|V_t|\le(1-\gamma)^{-1}|R_{\max}|\) 推出（模型已经对 \(Q_t\) 证明了同样的界）。这两个推导都还没有形式化。

**适用范围。** 状态与动作空间有限、奖励有界、折扣 \(\gamma<1\)；平均奖励、无折扣的回合制以及连续空间都不在范围内。参数空间 \(\Theta\) 是任意实赋范空间，所以并不局限于表格型参数化。所有陈述都针对精确期望和精确价值函数，不涉及方差、不涉及用学习到的 critic 做采样或自举估计、不涉及 \(\lambda<1\) 的 GAE，也不涉及随机梯度上升的收敛性。价值函数带有时间下标；模型证明了它们在可达状态上等于与时间无关的闭式，但定理陈述用的是带下标的版本。最后，每个定理的左边都是 \(\sum_t{}'\,\gamma^t\nabla_\theta\mathbb E_\theta[{\color{red}r}_t]\)，它与 \(\nabla_\theta J(\theta)\) 相等是另一条引理 (1)。

# 11 结论

我们在 Lean 4 与 mathlib 之上形式化了：带参数化策略的折扣 MDP 及其 Ionescu-Tulcea 轨迹分布；它的 Bellman 方程；价值函数梯度的递推，及其用归纳法展开得到的精确截断策略梯度恒等式；动作价值形式与 REINFORCE 形式下的极限；以及“把回报换成价值函数时序差分残差的折扣和，策略梯度不变”这一事实。证明只用到标准公理，而陈述中唯一看起来很强的假设其实没被用到，可以删去。

# 致谢

本形式化使用了 Lean 4 与 mathlib [2][22]。本文引用的各模块的交互式陈述见 [lemma.cn](http://www.lemma.cn/)。

# 参考文献

[1] Mark Chevallier, Jacques Fleuriot. Formalising the Foundations of Discrete Reinforcement Learning in Isabelle/HOL. 2021. [arXiv:2112.05996](https://arxiv.org/abs/2112.05996).

[2] Leonardo de Moura, Sebastian Ullrich. The Lean 4 Theorem Prover and Programming Language. CADE 28, LNCS 12699, pp. 625–635, Springer, 2021.

[3] Evan Greensmith, Peter L. Bartlett, Jonathan Baxter. Variance Reduction Techniques for Gradient Estimates in Reinforcement Learning. *Journal of Machine Learning Research* 5:1471–1530, 2004.

[4] Olav Kallenberg. *Foundations of Modern Probability*. 2nd ed., Springer, 2002.

[5] lean-dojo. TorchLean: Formalizing Neural Networks in Lean. GitHub repository, 2026. <https://github.com/lean-dojo/TorchLean>

[6] math-proof. lemma: machine-checked tensor calculus. 2026. <https://github.com/math-proof/lemma>

[7] math-proof. [Random.Expect_ConditionedGrad_LogProb.eq.Zero.policy](http://www.lemma.cn/lean/?module=Random.Expect_ConditionedGrad_LogProb.eq.Zero.policy). 2026.

[8] math-proof. [Real.Eq_0.Lim.of.LtAbs.IsFinite](http://www.lemma.cn/lean/?module=Real.Eq_0.Lim.of.LtAbs.IsFinite). 2026.

[9] math-proof. [Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman](http://www.lemma.cn/lean/?module=Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman). 2026.

[10] math-proof. [Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.IsFinite.Q_Function](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.IsFinite.Q_Function). 2026.

[11] math-proof. [Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.IsFinite.policy_gradient_theorem](http://www.lemma.cn/lean/?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.IsFinite.policy_gradient_theorem). 2026.

[12] math-proof. [Tensor.Eq.Expect.Grad.Log.Pr.of.Eq_Conditioned.Q_Function.discounted](http://www.lemma.cn/lean/?module=Tensor.Eq.Expect.Grad.Log.Pr.of.Eq_Conditioned.Q_Function.discounted). 2026.

[13] math-proof. [Tensor.Eq.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient](http://www.lemma.cn/lean/?module=Tensor.Eq.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient). 2026.

[14] math-proof. [Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.unbiased_advantage_estimate](http://www.lemma.cn/lean/?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.unbiased_advantage_estimate). 2026.

[15] math-proof. [Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.induct](http://www.lemma.cn/lean/?module=Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.induct). 2026.

[16] math-proof. [Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.recursion](http://www.lemma.cn/lean/?module=Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.recursion). 2026.

[17] Mathlib community. The Lean mathematical library. 2026. <https://leanprover-community.github.io/mathlib4_docs/>

[18] Martin L. Puterman. *Markov Decision Processes: Discrete Stochastic Dynamic Programming*. Wiley, 1994.

[19] John Schulman, Philipp Moritz, Sergey Levine, Michael Jordan, Pieter Abbeel. High-Dimensional Continuous Control Using Generalized Advantage Estimation. ICLR, 2016. [arXiv:1506.02438](https://arxiv.org/abs/1506.02438).

[20] Richard S. Sutton, Andrew G. Barto. *Reinforcement Learning: An Introduction*. 2nd ed., MIT Press, 2018.

[21] Richard S. Sutton, David McAllester, Satinder Singh, Yishay Mansour. Policy Gradient Methods for Reinforcement Learning with Function Approximation. NeurIPS 12, pp. 1057–1063, MIT Press, 2000.

[22] The mathlib Community. The Lean Mathematical Library. CPP, pp. 367–381, ACM, 2020.

[23] Koundinya Vajjha, Avraham Shinnar, Barry Trager, Vasily Pestun, Nathan Fulton. CertRL: Formalizing Convergence Proofs for Value and Policy Iteration in Coq. CPP, pp. 18–31, ACM, 2021. arXiv:2009.11403.

[24] Ronald J. Williams. Simple Statistical Gradient-Following Algorithms for Connectionist Reinforcement Learning. *Machine Learning* 8(3–4):229–256, 1992.

[25] Shangtong Zhang. rl-theory-in-lean: RLTheory/Algorithm/PolicyGradient.lean, commit 2a9d01a. GitHub, 2026-03-30. <https://github.com/ShangtongZhang/rl-theory-in-lean/commit/2a9d01a236961b1c9bc451a8926346364fc66e7f>（实验性的、主要由机器生成的开发，其提交与 AI 助手共同署名；2026 年 3 月提交，后来从该项目的 main 分支撤回，在该提交处仍可访问）
