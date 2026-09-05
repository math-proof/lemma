项目工件：<https://github.com/math-proof/lemma>

相对：[softmax](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxDivDot_Stack_TDot.eq.Stack_Div_SumExp.of.Eq_Stack_Mul)，配对：[配对](http://www.lemma.cn/lean/?module=Tensor.DotDotSRotaryMatrix.eq.Dot_DotRotaryMatrixSub)，布局：[共轭](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix%27.eq.DotDot_RotaryMatrix)，实现：[kernel](http://www.lemma.cn/lean/?module=Tensor.DotRotaryMatrix.eq.AddMulS)，加法：[群律](http://www.lemma.cn/lean/?module=Tensor.DotRotaryMatrixS.eq.RotaryMatrixAdd)，正交：[正交](http://www.lemma.cn/lean/?module=Tensor.DotT_RotaryMatrix.eq.Eye)

# 摘要

旋转位置编码（RoPE）用二维平面上的旋转把 token 下标写进 query 与 key。使其有用的恒等式——kernel 求值、正交、角度相加、以及注意力化到相对偏移——本身是标准的，但通常只对 \(2\times 2\) 块或固定几何频率写出，且未经机器检验。

我们在 `lemma` 库中用 Lean 4 展开一维 RoPE。对任意角向量 \(\alpha\in\mathbb{R}^{d}\)（此处 \(d\) 已是半维）定义两个矩阵 \(\mathrm{R}(\alpha),\mathrm{R}'(\alpha)\in\mathbb{R}^{(d+d)\times(d+d)}\)。不带撇的是 Hugging Face Transformers 的奇偶对半布局[[4]](https://github.com/huggingface/transformers/blob/main/docs/source/en/internal/rope_utils.md)；带撇的是苏剑林等原文的交错块对角布局[[2]](https://arxiv.org/abs/2104.09864)。二者被固定的奇偶聚集 \(\boldsymbol{P}\) 共轭：\(\mathrm{R}'(\alpha)=\boldsymbol{P}^{\top}\mathrm{R}(\alpha)\boldsymbol{P}\)，且逐元 \(\mathrm{R}'(\alpha)_{i,j}=\mathrm{R}(\alpha)_{i^{\mathrm{toSplit}},j^{\mathrm{toSplit}}}\)。

我们证明（无 `sorry`）：实现公式 \(\mathrm{R}(\alpha)\,x=x\odot\cos(\alpha\mathbin{+\mkern-4mu+}\alpha)+((-x_{1})\mathbin{+\mkern-4mu+}x_{0})\odot\sin(\alpha\mathbin{+\mkern-4mu+}\alpha)\)；正交 \(\mathrm{R}(\alpha)^{\top}\mathrm{R}(\alpha)=I_{d+d}\) 与 \(\mathrm{R}(-\alpha)=\mathrm{R}(\alpha)^{\top}\)；自由角群律 \(\mathrm{R}(\alpha)\mathrm{R}(\beta)=\mathrm{R}(\alpha+\beta)\)；RoFormer 配对 \((\mathrm{R}(\alpha)\,q)^{\top}(\mathrm{R}(\beta)\,k)=q^{\top}\mathrm{R}(\beta-\alpha)\,k\)；撇号布局上同样的转置积 \(\mathrm{R}'(\alpha)^{\top}\mathrm{R}'(\beta)=\mathrm{R}'(\beta-\alpha)\)；以及在线性假设 \(\theta_{i}=i\,\tau\) 下，softmax 注意力的相对形式——每个未归一化权重只依赖 \(\mathrm{R}(\theta_{k}-\theta_{i})\)，并可改写为 \(\mathrm{R}(\theta_{k-i})\) 或 \(\mathrm{R}(\theta_{i-k})^{\top}\)。交互陈述见 [lemma.cn](http://www.lemma.cn/)。

# 1 引言

Transformer 需要次序的表示[[5]](https://arxiv.org/abs/1706.03762)。旋转位置编码（RoPE）[[2]](https://arxiv.org/abs/2104.09864)[[3]](https://www.sciencedirect.com/science/article/pii/S0925231223011861) 对 query、key 的每一对通道，按依赖 token 下标的角度旋转。它现已是开源语言模型的默认位置偏置[[6]](https://arxiv.org/abs/2302.13971)。代数内容是古典的：平面旋转构成 \(\mathrm{SO}(2)\) 的交换子群，转置即逆，乘积加角。RoFormer 记下对注意力有用的推论

\[
\bigl(\mathrm{R}_{\Theta,m}\,q\bigr)^{\top}\bigl(\mathrm{R}_{\Theta,n}\,k\bigr)
= q^{\top} \mathrm{R}_{\Theta,n-m}\,k,
\]

并把相对矩阵写成转置积 \(\mathrm{R}_{\Theta,n-m}=(\mathrm{R}_{\Theta,m})^{\top}\mathrm{R}_{\Theta,n}\)。该式在 Lean 4 中机器检验为 [Tensor.DotDotSRotaryMatrix.eq.Dot_DotRotaryMatrixSub](http://www.lemma.cn/lean/?module=Tensor.DotDotSRotaryMatrix.eq.Dot_DotRotaryMatrixSub)；证明见 §8.1。后来的综述把 \(2\times 2\) 规则单独写出：\(\rho(\theta)^{\top}=\rho(-\theta)\)、\(\rho(\theta)\rho(\theta')=\rho(\theta+\theta')\)[[9]](https://arxiv.org/abs/2410.06205)。

这些恒等式在单个平面上用手算很容易，再经块对角直和抬上去。实现真正去乘的布局则不那么顺手：嵌入拆成前半与后半，平面 \(p\) 混合的是坐标 \(p\) 与 \(p+d\)，而非 \(2p\) 与 \(2p+1\)。高效求值

\[
\mathrm{R}(\alpha)\,x
= x \odot \cos(\alpha\mathbin{+\mkern-4mu+}\alpha)
+ \mathrm{rotateHalf}(x)\odot\sin(\alpha\mathbin{+\mkern-4mu+}\alpha)
\]

出现在 Hugging Face kernel[[4]](https://github.com/huggingface/transformers/blob/main/docs/source/en/internal/rope_utils.md)[[6]](https://arxiv.org/abs/2302.13971) 中，并不是上面配对式所写的交错矩阵。RoFormer 矩阵与 kernel 公式之间的缝，正适合机器检验。

本文在 Lean 4[[13]](https://link.springer.com/chapter/10.1007/978-3-030-79876-5_37) 上、在形状为自然数列表、矩阵乘为带类型 `Dot` 实例的 `lemma` 张量库[[1]](https://github.com/math-proof/lemma) 中记录这一发展。对象是两个自由角向量上的映射

\[
\mathrm{R},\;\mathrm{R}' : \mathbb{R}^{d} \to \mathbb{R}^{(d+d)\times(d+d)}：
\]

`rotaryMatrix` 是 Hugging Face 对半矩阵，`rotaryMatrix'` 是苏剑林等的原文交错矩阵。\(\mathrm{R}\) 不内建任何频率表。几何 RoPE 角 \(\theta_{i,p}=\lambda\,i/b^{p/d}\) 只在后文出现，且只作为常频率向量 \(\tau\in\mathbb{R}^{d}\) 的特例 \(\theta_{i}=i\,\tau\)。相对下标所需的算术仅此；YaRN 式缩放及其他学得或插值频率[[10]](https://arxiv.org/abs/2309.00071) 是同一条引理换一个 \(\tau\)。

**贡献。** 下列一维 RoPE 事实均经机器检验、无 `sorry`。每个公开名是库中的模块路径；路径即陈述。

1. **两种布局。** [RotaryMatrix.eq.AppendHstackSMulSEye](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix.eq.AppendHstackSMulSEye) 是 Hugging Face 的 `rotate_half`；[RotaryMatrix%27.eq.Stack_Ite_IteS](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix%27.eq.Stack_Ite_IteS) 是 RoFormer 矩阵。二者被奇偶聚集 \(\boldsymbol{P}=\mathrm{interleave}\,d\) 共轭：[RotaryMatrix%27.eq.DotDot_RotaryMatrix](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix%27.eq.DotDot_RotaryMatrix) 陈述 \(\mathrm{R}'(\alpha)=\boldsymbol{P}^{\top}\mathrm{R}(\alpha)\boldsymbol{P}\)，[GetRotaryMatrix%27.eq.GetRotaryMatrix](http://www.lemma.cn/lean/?module=Tensor.GetRotaryMatrix%27.eq.GetRotaryMatrix) 陈述逐元形式。
2. **实现。** [DotRotaryMatrix.eq.AddMulS](http://www.lemma.cn/lean/?module=Tensor.DotRotaryMatrix.eq.AddMulS)：Hugging Face 矩阵上的 kernel 公式。
3. **正交。** [DotT_RotaryMatrix.eq.Eye](http://www.lemma.cn/lean/?module=Tensor.DotT_RotaryMatrix.eq.Eye)：\(\mathrm{R}(\alpha)^{\top}\mathrm{R}(\alpha)=I_{d+d}\)，以及 \(\mathrm{R}(-\alpha)=\mathrm{R}(\alpha)^{\top}\) 与 \(\mathrm{R}(-\alpha)\mathrm{R}(\alpha)=I_{d+d}\)。
4. **可加。** [DotRotaryMatrixS.eq.RotaryMatrixAdd](http://www.lemma.cn/lean/?module=Tensor.DotRotaryMatrixS.eq.RotaryMatrixAdd)：\(\mathrm{R}(\alpha)\mathrm{R}(\beta)=\mathrm{R}(\alpha+\beta)\)，对任意角向量，不限于整数 token 下标。
5. **配对。** [DotDotSRotaryMatrix.eq.Dot_DotRotaryMatrixSub](http://www.lemma.cn/lean/?module=Tensor.DotDotSRotaryMatrix.eq.Dot_DotRotaryMatrixSub)：自由角上的 RoFormer 配对。RoFormer 布局上同样的转置积是 [DotT.eq.RotaryMatrix%27Sub](http://www.lemma.cn/lean/?module=Tensor.DotT.eq.RotaryMatrix%27Sub)：\(\mathrm{R}'(\alpha)^{\top}\mathrm{R}'(\beta)=\mathrm{R}'(\beta-\alpha)\)。
6. **相对注意力。** [DotSoftmaxDivDot_Stack_TDot.eq.Stack_Div_SumExp.of.Eq_Stack_Mul](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxDivDot_Stack_TDot.eq.Stack_Div_SumExp.of.Eq_Stack_Mul)：对每个 query、key 作用 \(\mathrm{R}(\theta_{i})\) 后，未归一化权重依赖 \(\mathrm{R}(\theta_{k}-\theta_{i})\)；在 \(\theta_{i}=i\,\tau\) 下该矩阵为 \(\mathrm{R}(\theta_{k-i})\) 或 \(\mathrm{R}(\theta_{i-k})^{\top}\)。

数学并不新。这里打包的是一对形式对象——RoFormer 矩阵与 Hugging Face 矩阵——二者之间已检验的共轭、不强于下标线性的频率假设，以及从 Hugging Face 定义到 softmax 恒等式的完整链条。

# 2 相关工作

RoFormer[[2]](https://arxiv.org/abs/2104.09864)[[3]](https://www.sciencedirect.com/science/article/pii/S0925231223011861) 引入 RoPE，在交错对 \((2p,\,2p+1)\) 上写出 \(2\times 2\) 旋转的块对角矩阵，并导出配对式。文中强调正交与内积的相对偏移形式。相对矩阵写成转置积 \(\mathrm{R}_{\Theta,n-m}=(\mathrm{R}_{\Theta,m})^{\top}\mathrm{R}_{\Theta,n}\)，而非自由角复合 \(\mathrm{R}(\alpha)\mathrm{R}(\beta)=\mathrm{R}(\alpha+\beta)\)。Hugging Face Transformers 使用共轭的对半布局，并以 `rotate_half` 求值[[4]](https://github.com/huggingface/transformers/blob/main/docs/source/en/internal/rope_utils.md)。两篇公开矩阵即下文（HF）与（Su）；本文对二者及共轭作机器检验。

加法律在后来的理论工作中已写出。Liu 等[[7]](https://arxiv.org/abs/2504.06308) 称之为指数可加性：若 \(XY=YX\)，则 \(\exp(X)\exp(Y)=\exp(X+Y)\)。在 Lie 参数 \(\mathrm{R}_{\boldsymbol{x}}=\exp(\sum_{i}x_{i}B_{i})\) 与交换生成元下，这正是 \(\mathrm{R}_{\boldsymbol{u}}\mathrm{R}_{\boldsymbol{v}}=\mathrm{R}_{\boldsymbol{u}+\boldsymbol{v}}\)，他们并记下 \(\mathrm{R}_{\boldsymbol{u}}^{\top}\mathrm{R}_{\boldsymbol{v}}=\mathrm{R}_{\boldsymbol{v}-\boldsymbol{u}}\)。Zhang 等[[8]](https://arxiv.org/abs/2512.07805) 写成单参数子群律 \(\mathbf{G}(n+m)=\mathbf{G}(n)\mathbf{G}(m)\)，把 RoPE 收为乘性 GRAPE。Barbero 等[[9]](https://arxiv.org/abs/2410.06205) 用整数特例 \(\rho(g)^{i}=\rho(ig)\)，故 \(\mathrm{R}^{i}\mathrm{R}^{j}=\mathrm{R}^{i+j}\)。YaRN 等上下文扩展[[10]](https://arxiv.org/abs/2309.00071) 保留此群律，只改频率。本文不把加法律当作新数学；只对 Hugging Face 矩阵与任意一对角向量作机器检验，并把转置积运到 RoFormer 矩阵。实现笔记[[6]](https://arxiv.org/abs/2302.13971)[[4]](https://github.com/huggingface/transformers/blob/main/docs/source/en/internal/rope_utils.md) 经 kernel 公式求值，而非稠密的 \((d+d)\times(d+d)\) 乘法。

更广的相对注意力包括 Shaw 等[[11]](https://aclanthology.org/N18-2074/) 与 ALiBi[[12]](https://arxiv.org/abs/2108.12409)。我们不比较方法，只认证旋转这一特例的代数。

形式化一侧，mathlib[[14]](https://dl.acm.org/doi/10.1145/3372885.3373824)[[15]](https://leanprover-community.github.io/mathlib4_docs/) 含我们实数与向量引理底下的三角加法公式，但没有 RoPE 矩阵或注意力恒等式。

# 3 张量与记号

环境类型是带形状的张量 \(\operatorname{Tensor}\,\mathbb{R}\,s\)，\(s:\mathrm{List}\,\mathbb{N}\)。长 \(d\) 的向量形状为 \([d]\)；\((d+d)\times(d+d)\) 矩阵形状为 \([d+d,\,d+d]\)。加减乘、余弦正弦皆逐点。矩阵乘写作 \(A @ B\)，是 `Dot` 类的实例，结果形状为 `matmul_shape`。两个 \(1\)-张量的内积仍写作 `@`；库把该标量包成 \(\operatorname{Tensor}\,\mathbb{R}\,[]\)。正交即 \(A^{\top} @ A = I\)。

全文 Lean 参数 \(d\) 是*半*维：嵌入宽为 \(d+d\)。这与奇偶（对半）配对一致，并避开宽度为偶数的旁条件。\(1\)-张量拼接记 \(\mathbin{+\mkern-4mu+}\)，逐点积记 \(\odot\)。下标 \(\theta[i]\) 是沿首轴的 `GetElem`。对 \(k,t:\mathrm{Fin}\,n\) 且 \(k\ge t\)，差 \(k-t\) 与值的减法一致（[Nat.ValSub.eq.SubValS.of.Ge](http://www.lemma.cn/lean/?module=Nat.ValSub.eq.SubValS.of.Ge)）。

\(\mathrm{R}(\alpha)\) 为 Lean 函数 `rotaryMatrix`（Hugging Face），\(\mathrm{R}'(\alpha)\) 为 `rotaryMatrix'`（RoFormer）。奇偶聚集为 \(\boldsymbol{P}=\mathrm{interleave}\,d\)。

# 4 旋转矩阵

库对同一角向量 \(\alpha\in\mathbb{R}^{d}\) 定义两个旋转矩阵，差别只在哪些坐标构成一个平面。下列阵列即相应引理 docstring 中的 LaTeX；二者都把公开矩阵写成 \({\boldsymbol{R}}^{d}_{\Theta,m}\)，而 Lean 的 \(d\) 是半维，故 \(\alpha\) 扮演 \((m\theta_{1},\ldots,m\theta_{d/2})\)，矩阵形状为 \([d+d,\,d+d]\)。

## 4.1 Hugging Face 对半矩阵

**定义 4.1**（对半旋转矩阵，[RotaryMatrix.eq.AppendHstackSMulSEye](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix.eq.AppendHstackSMulSEye)）。设 \(\alpha\in\mathbb{R}^{d}\)，\(I_{d}\) 为 \(d\times d\) 单位阵。定义

\[
\mathrm{R}(\alpha)
=
\begin{pmatrix}
I_{d} \odot \cos\alpha & -(I_{d} \odot \sin\alpha) \\
I_{d} \odot \sin\alpha & \phantom{-}I_{d} \odot \cos\alpha
\end{pmatrix}
\in \mathbb{R}^{(d+d)\times(d+d)},
\]

其中 \(\odot\) 把向量 \(\cos\alpha\)（或 \(\sin\alpha\)）广播到各块的对角。库中这是两行水平拼接再竖直拼接。

这是 Hugging Face Transformers 的奇偶布局[[4]](https://github.com/huggingface/transformers/blob/main/docs/source/en/internal/rope_utils.md)：平面 \(p\) 为对 \((p,\,p+d)\)，与 `rotate_half` 一致。引理 docstring 把同一矩阵写成公开的展开式

\[
{\boldsymbol{R}}^{d}_{\Theta,m}=\begin{pmatrix}
\cos m\theta_{1} & 0 & \cdots & 0 & -\sin m\theta_{1} & 0 & \cdots & 0 \\
0 & \cos m\theta_{2} & \cdots & 0 & 0 & -\sin m\theta_{2} & \cdots & 0 \\
\vdots & \vdots & \ddots & \vdots & \vdots & \vdots & \ddots & \vdots \\
0 & 0 & \cdots & \cos m\theta_{d/2} & 0 & 0 & \cdots & -\sin m\theta_{d/2} \\
\sin m\theta_{1} & 0 & \cdots & 0 & \cos m\theta_{1} & 0 & \cdots & 0 \\
0 & \sin m\theta_{2} & \cdots & 0 & 0 & \cos m\theta_{2} & \cdots & 0 \\
\vdots & \vdots & \ddots & \vdots & \vdots & \vdots & \ddots & \vdots \\
0 & 0 & \cdots & \sin m\theta_{d/2} & 0 & 0 & \cdots & \cos m\theta_{d/2}
\end{pmatrix}.
\]

块形式即此展开式。作用于对半向量 \(x=x_{0}\mathbin{+\mkern-4mu+}x_{1}\)（\(x_{0},x_{1}\in\mathbb{R}^{d}\)）时，定义为同时的平面旋转

\[
\begin{pmatrix} y_{0,p} \\ y_{1,p} \end{pmatrix}
=
\begin{pmatrix}
\cos\alpha_{p} & -\sin\alpha_{p} \\
\sin\alpha_{p} & \phantom{-}\cos\alpha_{p}
\end{pmatrix}
\begin{pmatrix} x_{0,p} \\ x_{1,p} \end{pmatrix}.
\]

## 4.2 RoFormer 交错矩阵

**定义 4.2**（交错旋转矩阵，[RotaryMatrix%27.eq.Stack_Ite_IteS](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix%27.eq.Stack_Ite_IteS)）。苏剑林等原文[[2]](https://arxiv.org/abs/2104.09864) 的旋转矩阵作用在交错对 \((2p,\,2p+1)\)（一基下标 \((2i-1,\,2i)\)）。引理 docstring 记下

\[
{\boldsymbol{R}}^{d}_{\Theta,m}=\begin{pmatrix}
\cos m\theta_{1} & -\sin m\theta_{1} & 0 & 0 & \cdots & 0 & 0 \\
\sin m\theta_{1} & \cos m\theta_{1} & 0 & 0 & \cdots & 0 & 0 \\
0 & 0 & \cos m\theta_{2} & -\sin m\theta_{2} & \cdots & 0 & 0 \\
0 & 0 & \sin m\theta_{2} & \cos m\theta_{2} & \cdots & 0 & 0 \\
\vdots & \vdots & \vdots & \vdots & \ddots & \vdots & \vdots \\
0 & 0 & 0 & 0 & \cdots & \cos m\theta_{d/2} & -\sin m\theta_{d/2} \\
0 & 0 & 0 & 0 & \cdots & \sin m\theta_{d/2} & \cos m\theta_{d/2}
\end{pmatrix}.
\]

我们把此矩阵记为 \(\mathrm{R}'(\alpha)\)。偶数行 \(i=2p\) 上非零元是对角的 \(\cos\alpha_{p}\) 与右侧紧邻的 \(-\sin\alpha_{p}\)；下一行是左侧紧邻的 \(\sin\alpha_{p}\) 与对角的 \(\cos\alpha_{p}\)（[GetRotaryMatrix%27.eq.Ite_IteS](http://www.lemma.cn/lean/?module=Tensor.GetRotaryMatrix%27.eq.Ite_IteS)）。

## 4.3 对照

两种布局只差一个与 \(\alpha\) 无关的固定奇偶聚集。

**定义 4.3**（奇偶聚集，[Interleave.eq.AppendStackS_Delta](http://www.lemma.cn/lean/?module=Tensor.Interleave.eq.AppendStackS_Delta)）。令 \(\boldsymbol{P}:=\mathrm{interleave}\,d\in\mathbb{R}^{(d+d)\times(d+d)}\) 为引理 docstring 中的置换阵

\[
{\boldsymbol{P}}=\begin{pmatrix}
1 & 0 & 0 & 0 & \cdots & 0 & 0 \\
0 & 0 & 1 & 0 & \cdots & 0 & 0 \\
\vdots & \vdots & \vdots & \vdots & \ddots & \vdots & \vdots \\
0 & 0 & 0 & 0 & \cdots & 1 & 0 \\
0 & 1 & 0 & 0 & \cdots & 0 & 0 \\
0 & 0 & 0 & 1 & \cdots & 0 & 0 \\
\vdots & \vdots & \vdots & \vdots & \ddots & \vdots & \vdots \\
0 & 0 & 0 & 0 & \cdots & 0 & 1
\end{pmatrix},
\]

于是 \((\boldsymbol{P}x)_{i}=x_{2i}\)、\((\boldsymbol{P}x)_{i+d}=x_{2i+1}\)。

\(\boldsymbol{P}\) 正交：\(\boldsymbol{P}^{\top}@\boldsymbol{P}=I_{d+d}\)（[DotTInterleave.eq.Eye](http://www.lemma.cn/lean/?module=Tensor.DotTInterleave.eq.Eye)），且 \(\boldsymbol{P}@\boldsymbol{P}^{\top}=I_{d+d}\)（[Dot_TInterleave.eq.Eye](http://www.lemma.cn/lean/?module=Tensor.Dot_TInterleave.eq.Eye)）。

**定理 4.4**（共轭，[RotaryMatrix%27.eq.DotDot_RotaryMatrix](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix%27.eq.DotDot_RotaryMatrix)）。对每一 \(\alpha\in\mathbb{R}^{d}\)，

\[
\mathrm{R}'(\alpha)
=
\bigl((\mathrm{interleave}\,d)^{\top} @ \mathrm{R}(\alpha)\bigr) @ \mathrm{interleave}\,d.
\]

故 \(\mathrm{R}'(\alpha)=\boldsymbol{P}^{\top}\mathrm{R}(\alpha)\boldsymbol{P}\)：交错向量先被聚到对半布局，经 Hugging Face 矩阵旋转，再散射回去。展开式的四个象限变成交错矩阵的 \(2\times 2\) 块。

逐元则是坐标重标号。

**引理 4.5**（[Fin.ToSplit.eq.Ite_Div_2](http://www.lemma.cn/lean/?module=Fin.ToSplit.eq.Ite_Div_2)）。对 \(i:\mathrm{Fin}\,(d+d)\)，

\[
i^{\mathrm{toSplit}}
=
\begin{cases}
i/2 & \text{\(i\) 为偶},\\
i/2+d & \text{\(i\) 为奇}.
\end{cases}
\]

交错的偶数下落在前半，奇数下落在后半。

**定理 4.6**（逐元对照，[GetRotaryMatrix%27.eq.GetRotaryMatrix](http://www.lemma.cn/lean/?module=Tensor.GetRotaryMatrix%27.eq.GetRotaryMatrix)）。对每一 \(\alpha\in\mathbb{R}^{d}\) 与 \(i,j:\mathrm{Fin}\,(d+d)\)，

\[
\mathrm{R}'(\alpha)_{i,j}
=
\mathrm{R}(\alpha)_{i^{\mathrm{toSplit}},\,j^{\mathrm{toSplit}}}.
\]

四个象限对应四条象限引理：[MulCos_Delta.of.Lt.Lt](http://www.lemma.cn/lean/?module=Tensor.GetRotaryMatrix.eq.MulCos_Delta.of.Lt.Lt)、[MulCos_Delta.of.Ge.Ge](http://www.lemma.cn/lean/?module=Tensor.GetRotaryMatrix.eq.MulCos_Delta.of.Ge.Ge)、[MulSin_Delta.of.Ge.Lt](http://www.lemma.cn/lean/?module=Tensor.GetRotaryMatrix.eq.MulSin_Delta.of.Ge.Lt)、[MulNegSin_Delta.of.Lt.Ge](http://www.lemma.cn/lean/?module=Tensor.GetRotaryMatrix.eq.MulNegSin_Delta.of.Lt.Ge)。

Kernel 实现（§5）是关于 \(\mathrm{R}\) 的陈述，因为那是 `rotate_half` 实现的布局。§8.1 的配对链对 \(\mathrm{R}\) 写出；\(\mathrm{R}'\) 上匹配的矩阵恒等式是定理 7.2。

# 5 实现公式

稠密地乘对半矩阵并不是 Hugging Face RoPE 的跑法。Kernel 形式只要一份余弦、一份正弦，再加一次半交换。

**定理 5.1**（实现，[DotRotaryMatrix.eq.AddMulS](http://www.lemma.cn/lean/?module=Tensor.DotRotaryMatrix.eq.AddMulS)）。设 \(\alpha\in\mathbb{R}^{d}\)、\(x\in\mathbb{R}^{d+d}\)，并写

\[
x_{0}:=\mathrm{cast}(x_{[:d]}),\qquad
x_{1}:=\mathrm{cast}(x_{[d:]}),
\]

其中 cast 沿 [List.ConsLengthSlice.eq.List](http://www.lemma.cn/lean/?module=List.ConsLengthSlice.eq.List) 搬运依赖切片形状。则

\[
\mathrm{R}(\alpha)\,@\,x
=
x \odot \bigl(\cos(\alpha\mathbin{+\mkern-4mu+}\alpha)\bigr)
+
\bigl((-x_{1})\mathbin{+\mkern-4mu+}x_{0}\bigr) \odot \bigl(\sin(\alpha\mathbin{+\mkern-4mu+}\alpha)\bigr).
\]

证明先在库的形状 cast 相等 \(\simeq\) 下认出 \(x=x_{0}\mathbin{+\mkern-4mu+}x_{1}\)，再套已拆开的恒等式 [DotRotaryMatrix.eq.AddMulSAppend](http://www.lemma.cn/lean/?module=Tensor.DotRotaryMatrix.eq.AddMulSAppend)：展开定义 4.1，四块乘 \(x_{0}\mathbin{+\mkern-4mu+}x_{1}\)，再拼回。\((-x_{1})\mathbin{+\mkern-4mu+}x_{0}\) 正是 Hugging Face 的 `rotate_half`[[4]](https://github.com/huggingface/transformers/blob/main/docs/source/en/internal/rope_utils.md)。定理 5.1 因此证明 kernel 与 Hugging Face 矩阵是同一映射。交错矩阵 \(\mathrm{R}'\) 随后由定理 4.4 恢复。

# 6 正交性

每一对坐标 \((x_{0,p},x_{1,p})\) 被标准 \(2\times 2\) 矩阵

\[
\rho(\alpha_{p})
=
\begin{pmatrix}
\cos\alpha_{p} & -\sin\alpha_{p} \\
\sin\alpha_{p} & \phantom{-}\cos\alpha_{p}
\end{pmatrix}
\]

旋转。它属于 \(\mathrm{SO}(2)\)：保欧氏长度的保向平面线性映射，等价于 \(\{A\in\mathbb{R}^{2\times 2}:A^{\top}A=I_{2},\;\det A=1\}\)。对半矩阵 \(\mathrm{R}(\alpha)\) 在每一平面 \(p\) 独立作用一个 \(\rho(\alpha_{p})\)，故 \(\mathrm{R}(\alpha)\) 自身落在 \(\mathrm{SO}(d+d)\)。

**引理 6.1**（[RotaryMatrixNeg.eq.TRotaryMatrix](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrixNeg.eq.TRotaryMatrix)）。对每一 \(\alpha\in\mathbb{R}^{d}\)，\(\mathrm{R}(-\alpha)=\mathrm{R}(\alpha)^{\top}\)。

证明是奇偶恒等式 \(\cos(-\alpha)=\cos\alpha\)、\(\sin(-\alpha)=-\sin\alpha\)（[CosNeg.eq.Cos](http://www.lemma.cn/lean/?module=Tensor.CosNeg.eq.Cos)、[SinNeg.eq.NegSin](http://www.lemma.cn/lean/?module=Tensor.SinNeg.eq.NegSin)），以及 \(2\times 2\) 水平拼接堆的块转置（[TAppendHstackS.eq.AppendHstackSTS](http://www.lemma.cn/lean/?module=Tensor.TAppendHstackS.eq.AppendHstackSTS)）。

**引理 6.2**（[RotaryMatrix0.eq.Eye](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix0.eq.Eye)）。\(\mathrm{R}(0)=I_{d+d}\)。RoFormer 布局同一条：[RotaryMatrix%270.eq.Eye](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix%270.eq.Eye) 陈述 \(\mathrm{R}'(0)=I_{d+d}\)。

这是 \(\cos 0=1\)、\(\sin 0=0\)（[Cos0.eq.One](http://www.lemma.cn/lean/?module=Tensor.Cos0.eq.One)、[Sin0.eq.Zero](http://www.lemma.cn/lean/?module=Tensor.Sin0.eq.Zero)）与块恒等式 [AppendHstackS.eq.Eye](http://www.lemma.cn/lean/?module=Tensor.AppendHstackS.eq.Eye)。

**定理 6.3**（正交，[DotT_RotaryMatrix.eq.Eye](http://www.lemma.cn/lean/?module=Tensor.DotT_RotaryMatrix.eq.Eye)）。对每一 \(\alpha\in\mathbb{R}^{d}\)，

\[
\mathrm{R}(\alpha)^{\top} @ \mathrm{R}(\alpha) = I_{d+d}.
\]

由 §7 的差恒等式得 \(\mathrm{R}(\alpha)^{\top}@\mathrm{R}(\alpha)=\mathrm{R}(\alpha-\alpha)=\mathrm{R}(0)\)，再套引理 6.2。结合引理 6.1 得另一侧左逆（[DotRotaryMatrixNeg.eq.Eye](http://www.lemma.cn/lean/?module=Tensor.DotRotaryMatrixNeg.eq.Eye)）：\(\mathrm{R}(-\alpha)\,@\,\mathrm{R}(\alpha)=I_{d+d}\)。

# 7 可加性

**定理 7.1**（转置积，[DotT.eq.RotaryMatrixSub](http://www.lemma.cn/lean/?module=Tensor.DotT.eq.RotaryMatrixSub)）。对所有 \(\alpha,\beta\in\mathbb{R}^{d}\)，

\[
\mathrm{R}(\alpha)^{\top} @ \mathrm{R}(\beta) = \mathrm{R}(\beta-\alpha).
\]

这是 RoFormer 对 \(\mathrm{R}_{\Theta,n-m}\) 的定义在自由角、Hugging Face 矩阵上的形式。证明展开定义 4.1 两侧，乘四乘四的块型（[DotAppendSHstackS.eq.AppendHstackSAddSDotS](http://www.lemma.cn/lean/?module=Tensor.DotAppendSHstackS.eq.AppendHstackSAddSDotS)、[DotMulSEye.eq.MulEye](http://www.lemma.cn/lean/?module=Tensor.DotMulSEye.eq.MulEye)），并套张量余弦、正弦减法

\[
\begin{align*}
\cos(\beta-\alpha)&=\cos\alpha\odot\cos\beta+\sin\alpha\odot\sin\beta,\\
\sin(\beta-\alpha)&=\sin\beta\odot\cos\alpha-\cos\beta\odot\sin\alpha,
\end{align*}
\]

即 [CosSub.eq.AddMulS](http://www.lemma.cn/lean/?module=Tensor.CosSub.eq.AddMulS) 与 [SinSub.eq.SubMulSSin_Cos](http://www.lemma.cn/lean/?module=Tensor.SinSub.eq.SubMulSSin_Cos)。

RoFormer 矩阵由共轭满足同一律。

**定理 7.2**（[DotT.eq.RotaryMatrix%27Sub](http://www.lemma.cn/lean/?module=Tensor.DotT.eq.RotaryMatrix%27Sub)）。对所有 \(\alpha,\beta\in\mathbb{R}^{d}\)，

\[
\mathrm{R}'(\alpha)^{\top} @ \mathrm{R}'(\beta) = \mathrm{R}'(\beta-\alpha).
\]

证明写 \(\mathrm{R}'(\alpha)=\boldsymbol{P}^{\top}\mathrm{R}(\alpha)\boldsymbol{P}\)（定理 4.4），消去 \(\boldsymbol{P}^{\top}@\boldsymbol{P}=I\) 与 \(\boldsymbol{P}@\boldsymbol{P}^{\top}=I\)，再套定理 7.1。

**定理 7.3**（加法群律，[DotRotaryMatrixS.eq.RotaryMatrixAdd](http://www.lemma.cn/lean/?module=Tensor.DotRotaryMatrixS.eq.RotaryMatrixAdd)）。对所有 \(\alpha,\beta\in\mathbb{R}^{d}\)，

\[
\mathrm{R}(\alpha)\,@\,\mathrm{R}(\beta) = \mathrm{R}(\alpha+\beta).
\]

把 \(\alpha+\beta=\beta-(-\alpha)\)（`add_comm`，[Int.Add.eq.Sub_Neg](http://www.lemma.cn/lean/?module=Int.Add.eq.Sub_Neg)）与 \(\alpha=-(-\alpha)\) 代入。引理 6.1 给出 \(\mathrm{R}(\alpha)=\mathrm{R}(-\alpha)^{\top}\)。定理 7.1 再得 \(\mathrm{R}(-\alpha)^{\top}@\mathrm{R}(\beta)=\mathrm{R}(\beta-(-\alpha))\)。

这是 Liu 等[[7]](https://arxiv.org/abs/2504.06308) 与 Zhang 等[[8]](https://arxiv.org/abs/2512.07805) 已陈述的可加性在对半、自由角上的形式。此处对完整对半矩阵与任意一对角向量成立：没有 token 下标，也没有几何频率表。特例 \(\beta=\alpha\) 经 \(\mathrm{R}(0)=I\) 回到定理 6.3。

把定理 7.1 与 \(\theta\) 对下标的线性合成，得到按 token 下标的形式。

**命题 7.4**（[DotT.eq.RotaryMatrixSub.of.Eq_Stack_Mul.Ge](http://www.lemma.cn/lean/?module=Tensor.DotT.eq.RotaryMatrixSub.of.Eq_Stack_Mul.Ge)）。设 \(\theta\in\mathbb{R}^{n\times d}\) 满足 \(\theta_{i}=i\,\tau\)（固定 \(\tau\in\mathbb{R}^{d}\)），且 \(k,t:\mathrm{Fin}\,n\)、\(k\ge t\)。则

\[
\mathrm{R}(\theta_{t})^{\top} @ \mathrm{R}(\theta_{k}) = \mathrm{R}(\theta_{k-t}).
\]

RoFormer 布局上同一算术是 [DotT.eq.RotaryMatrix%27Get_Sub.of.Eq_Stack_Mul.Ge](http://www.lemma.cn/lean/?module=Tensor.DotT.eq.RotaryMatrix%27Get_Sub.of.Eq_Stack_Mul.Ge)：\(\mathrm{R}'(\theta_{t})^{\top}@\mathrm{R}'(\theta_{k})=\mathrm{R}'(\theta_{k-t})\)。

定理 7.1 之外唯一的算术是 \(\theta_{k}-\theta_{t}=\theta_{k-t}\)（[SubGetS.eq.Get_Sub.of.Eq_Stack_Mul.Ge](http://www.lemma.cn/lean/?module=Tensor.SubGetS.eq.Get_Sub.of.Eq_Stack_Mul.Ge)），即一旦把 \(k-t\) 读成值而非回绕，便是 \((k-t)\tau\)（[Nat.CoeSub.eq.SubCoeS.of.Ge](http://www.lemma.cn/lean/?module=Nat.CoeSub.eq.SubCoeS.of.Ge)）。

# 8 注意力中的相对位置

## 8.1 两个旋转向量的配对

RoFormer 的相对位置律是内积恒等式

\[
\bigl(\mathrm{R}_{\Theta,m}\,q\bigr)^{\top}\bigl(\mathrm{R}_{\Theta,n}\,k\bigr)
= q^{\top} \mathrm{R}_{\Theta,n-m}\,k.
\]

库对自由角向量证明此事，无频率假设。两个 \(1\)-张量的内积写作 `@`，故上式定义上即

\[
\bigl(\mathrm{R}(\alpha)\,@\,q\bigr)\,@\,\bigl(\mathrm{R}(\beta)\,@\,k\bigr)
=
q\,@\,\bigl(\mathrm{R}(\beta-\alpha)\,@\,k\bigr).
\]

对应为 \(\alpha\leftrightarrow\Theta_{m}\)、\(\beta\leftrightarrow\Theta_{n}\)，从而角空间中 \(\beta-\alpha\leftrightarrow n-m\)。Lean 4 陈述（完整证明、无 `sorry`）为 [Tensor.DotDotSRotaryMatrix.eq.Dot_DotRotaryMatrixSub](http://www.lemma.cn/lean/?module=Tensor.DotDotSRotaryMatrix.eq.Dot_DotRotaryMatrixSub)。

**定理 8.1**（RoFormer 配对）。对 \(\alpha,\beta\in\mathbb{R}^{d}\) 与 \(q,k\in\mathbb{R}^{d+d}\)，上式成立。

Lean 证明是如下链条。先把向量–矩阵积挪过内积（[Dot_T.eq.Dot](http://www.lemma.cn/lean/?module=Tensor.Dot_T.eq.Dot)）：

\[
(\mathrm{R}(\alpha)\,@\,q)\,@\,(\mathrm{R}(\beta)\,@\,k)
=
\bigl(q\,@\,\mathrm{R}(\alpha)^{\top}\bigr)\,@\,(\mathrm{R}(\beta)\,@\,k).
\]

向量–矩阵–向量情形的 `@` 结合律（[DotDot.eq.Dot_Dot](http://www.lemma.cn/lean/?module=Tensor.DotDot.eq.Dot_Dot)，实例 `vmv`）给出

\[
\bigl(q\,@\,\mathrm{R}(\alpha)^{\top}\bigr)\,@\,(\mathrm{R}(\beta)\,@\,k)
=
q\,@\,\bigl(\mathrm{R}(\alpha)^{\top} @ (\mathrm{R}(\beta)\,@\,k)\bigr).
\]

第二次结合（实例 `mmv`）把两个旋转矩阵拉到一起：

\[
\mathrm{R}(\alpha)^{\top} @ (\mathrm{R}(\beta)\,@\,k)
=
\bigl(\mathrm{R}(\alpha)^{\top} @ \mathrm{R}(\beta)\bigr)\,@\,k.
\]

定理 7.1 把矩阵积换成角差上的单个旋转矩阵 \(\mathrm{R}(\alpha)^{\top}@\mathrm{R}(\beta)=\mathrm{R}(\beta-\alpha)\)。代回即得配对式。

定理 8.1 中没有 token 下标，也没有 \(\Theta\) 上的频率表。古典记号 \(\mathrm{R}_{\Theta,n-m}\) 在下一小节、用 \(\theta_{i}=i\,\tau\) 把 \(\beta-\alpha\) 认成 \(\theta\) 的一行之后恢复。

## 8.2 线性频率

相对*下标*——用 \(\theta\) 自身的一行替换 \(\theta_{k}-\theta_{i}\)——需要 \(\theta\) 各行之间的关系。

**定义 8.2**（线性频率假设）。张量 \(\theta\in\mathbb{R}^{n\times d}\) 对 token 下标线性，是指存在 \(\tau\in\mathbb{R}^{d}\) 使

\[
\theta = \bigl[\,i < n\,\bigr]\;(\tau\cdot i)
\qquad\text{即}\qquad
\theta_{i} = i\,\tau\in\mathbb{R}^{d}.
\]

Lean 中此假设为 `hθ : θ = [i < n] (τ * (i : ℝ))`。标准 RoPE 是实例 \(\tau_{p}=\lambda/b^{p/d}\)。下列引理从不提及 \(b\) 或 \(\lambda\)。

**引理 8.3**（[RotaryMatrixSubGetS.eq.Ite_RotaryMatrix_T.of.Eq_Stack_Mul](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrixSubGetS.eq.Ite_RotaryMatrix_T.of.Eq_Stack_Mul)）。在定义 8.2 下，对所有 \(i,j:\mathrm{Fin}\,n\)，

\[
\mathrm{R}(\theta_{j}-\theta_{i})
=
\begin{cases}
\mathrm{R}(\theta_{j-i}) & \text{若 }j\ge i,\\
\mathrm{R}(\theta_{i-j})^{\top} & \text{若 }j<i.
\end{cases}
\]

非负支是 \(\theta_{j}-\theta_{i}=\theta_{j-i}\)。负支是 \(\theta_{j}-\theta_{i}=-(\theta_{i}-\theta_{j})=-\theta_{i-j}\) 加引理 6.1。库证明用 `erw [if_pos]` / `erw [if_neg]`：普通 `rw` 打不着 \(\mathrm{Fin}\,n\) 上 `GetElem` 的 \(\le\) 实例。

必要性（我们不另写引理）略弱：\(\mathrm{R}\) 只经 \((\cos,\sin)\) 依赖角度，故 \(j\ge i\) 时分量地 \(\theta_{j}-\theta_{i}\equiv\theta_{j-i}\pmod{2\pi}\) 已够。定义 8.2 是该同余的干净生成元。我们保留张量相等而非同余，以免另发展 \(2\pi\mathbb{Z}\)。

## 8.3 Softmax 注意力

设 \(Q,K,V\in\mathbb{R}^{n\times(d+d)}\)，写 \(R(i):=\mathrm{R}(\theta_{i})\)。RoPE 注意力映射为

\[
\operatorname{softmax}\!\left(\frac{Q^{R} (K^{R})^{\top}}{\sqrt{d+d}}\right) @ V,
\qquad
Q^{R}_{i} = R(i)\,@\,Q_{i},\quad
K^{R}_{i} = R(i)\,@\,K_{i}.
\]

**定理 8.4**（相对 softmax，[DotSoftmaxDivDot_Stack_TDot.eq.Stack_Div_SumExp.of.Eq_Stack_Mul](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxDivDot_Stack_TDot.eq.Stack_Div_SumExp.of.Eq_Stack_Mul)）。在定义 8.2 下，上式等于

\[
\Biggl[
i < n,\;
j < d+d
\Biggr]
\frac{
\sum_{k}
V_{k,j}\,
\exp\Bigl(
Q_{i} @ \bigl(\mathrm{Rel}(i,k)\,@\,K_{k}\bigr)
\big/\sqrt{d+d}
\Bigr)
}{
\sum\exp\Bigl(
\bigl(R(i)\,@\,Q_{i}\bigr)
@
(K^{R})^{\top}
\big/\sqrt{d+d}
\Bigr)
},
\]

其中相对矩阵来自引理 8.3，

\[
\mathrm{Rel}(i,k)
=
\begin{cases}
R(k-i) & \text{若 }k\ge i,\\
R(i-k)^{\top} & \text{若 }k<i,
\end{cases}
\]

分母是 query \(i\) 整行 logit（形状 \([n]\)）的指数和，仍保持旋转形式。

证明是按堆展开 softmax（[DotSoftmaxDivDot_T.eq.Stack_Div_SumExp](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxDivDot_T.eq.Stack_Div_SumExp)），再在每个分子项上对 \((i,k)\) 用定理 8.1、对所得角差用引理 8.3。对 \(Q,K,V\) 无额外假设。

两点簿记与 Lean 陈述完全对齐。第一，\(\mathrm{Rel}\) 用 \(R\) 绑定，不再第二次写出 `rotaryMatrix`，故相对矩阵定义上就是旋转矩阵或其转置。第二，配分函数不用 \(\mathrm{Rel}\) 改写：它仍是 \(\sum\exp\bigl((R(i)@Q_{i})@(K^{R})^{\top}/\sqrt{d+d}\bigr)\)。两种形式由同一配对相等，但已认证的恒等式只改写乘 \(V\) 的那些权重。

这就是「RoPE 是相对位置编码」的含义：旋转作用之后，每个未归一化权重是未旋转 query 与只依赖 \(k-i\) 的矩阵所旋转的 key 的普通内积。

# 9 形式化工件

已完成陈述的交互可视化：

- 相对 softmax：[DotSoftmaxDivDot_Stack_TDot.eq.Stack_Div_SumExp.of.Eq_Stack_Mul](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxDivDot_Stack_TDot.eq.Stack_Div_SumExp.of.Eq_Stack_Mul)
- RoFormer 配对：[DotDotSRotaryMatrix.eq.Dot_DotRotaryMatrixSub](http://www.lemma.cn/lean/?module=Tensor.DotDotSRotaryMatrix.eq.Dot_DotRotaryMatrixSub)
- 共轭 \(R'=P^{\top}RP\)：[RotaryMatrix%27.eq.DotDot_RotaryMatrix](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix%27.eq.DotDot_RotaryMatrix)
- Hugging Face 矩阵：[RotaryMatrix.eq.AppendHstackSMulSEye](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix.eq.AppendHstackSMulSEye)
- RoFormer 矩阵：[RotaryMatrix%27.eq.Stack_Ite_IteS](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix%27.eq.Stack_Ite_IteS)
- 实现：[DotRotaryMatrix.eq.AddMulS](http://www.lemma.cn/lean/?module=Tensor.DotRotaryMatrix.eq.AddMulS)
- 加法群律：[DotRotaryMatrixS.eq.RotaryMatrixAdd](http://www.lemma.cn/lean/?module=Tensor.DotRotaryMatrixS.eq.RotaryMatrixAdd)
- 正交：[DotT_RotaryMatrix.eq.Eye](http://www.lemma.cn/lean/?module=Tensor.DotT_RotaryMatrix.eq.Eye)

源码：<https://github.com/math-proof/lemma>[[1]](https://github.com/math-proof/lemma)。表中每个模块均 `lake build` 通过，且无 `sorry`。

所用余弦、正弦事实先在 \(\mathbb{R}\) 上证明，再到 `List.Vector`，再到张量，沿 `.data` 搬运。分层是故意的：旋转证明从不把张量实现展开到对应向量引理之外。

## 9.1 引理依赖

下列为标题引理所 import 的主要模块。链接指向 Lean 4 页。前缀 `Tensor.` 省略。

- [DotSoftmaxDivDot_Stack_TDot.eq.Stack_Div_SumExp.of.Eq_Stack_Mul](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxDivDot_Stack_TDot.eq.Stack_Div_SumExp.of.Eq_Stack_Mul) — 相对 softmax
  - [DotSoftmaxDivDot_T.eq.Stack_Div_SumExp](http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxDivDot_T.eq.Stack_Div_SumExp)
  - [DotDotSRotaryMatrix.eq.Dot_DotRotaryMatrixSub](http://www.lemma.cn/lean/?module=Tensor.DotDotSRotaryMatrix.eq.Dot_DotRotaryMatrixSub) — 配对
    - [DotT.eq.RotaryMatrixSub](http://www.lemma.cn/lean/?module=Tensor.DotT.eq.RotaryMatrixSub)
  - [RotaryMatrixSubGetS.eq.Ite_RotaryMatrix_T.of.Eq_Stack_Mul](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrixSubGetS.eq.Ite_RotaryMatrix_T.of.Eq_Stack_Mul)
    - [SubGetS.eq.Get_Sub.of.Eq_Stack_Mul.Ge](http://www.lemma.cn/lean/?module=Tensor.SubGetS.eq.Get_Sub.of.Eq_Stack_Mul.Ge)
    - [RotaryMatrixNeg.eq.TRotaryMatrix](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrixNeg.eq.TRotaryMatrix)
- [DotRotaryMatrixS.eq.RotaryMatrixAdd](http://www.lemma.cn/lean/?module=Tensor.DotRotaryMatrixS.eq.RotaryMatrixAdd) — 群律
  - [DotT.eq.RotaryMatrixSub](http://www.lemma.cn/lean/?module=Tensor.DotT.eq.RotaryMatrixSub)
  - [RotaryMatrixNeg.eq.TRotaryMatrix](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrixNeg.eq.TRotaryMatrix)
- [DotT_RotaryMatrix.eq.Eye](http://www.lemma.cn/lean/?module=Tensor.DotT_RotaryMatrix.eq.Eye) — 正交
  - [DotT.eq.RotaryMatrixSub](http://www.lemma.cn/lean/?module=Tensor.DotT.eq.RotaryMatrixSub)
  - [RotaryMatrix0.eq.Eye](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix0.eq.Eye)
- [DotRotaryMatrix.eq.AddMulS](http://www.lemma.cn/lean/?module=Tensor.DotRotaryMatrix.eq.AddMulS) — 实现
  - [DotRotaryMatrix.eq.AddMulSAppend](http://www.lemma.cn/lean/?module=Tensor.DotRotaryMatrix.eq.AddMulSAppend)
- [RotaryMatrix%27.eq.DotDot_RotaryMatrix](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix%27.eq.DotDot_RotaryMatrix) — 共轭
  - [GetRotaryMatrix%27.eq.Ite_IteS](http://www.lemma.cn/lean/?module=Tensor.GetRotaryMatrix%27.eq.Ite_IteS)
  - [GetRotaryMatrix.eq.MulCos_Delta.of.Lt.Lt](http://www.lemma.cn/lean/?module=Tensor.GetRotaryMatrix.eq.MulCos_Delta.of.Lt.Lt) 等四象限
- [DotT.eq.RotaryMatrix%27Sub](http://www.lemma.cn/lean/?module=Tensor.DotT.eq.RotaryMatrix%27Sub) — 撇号转置积
  - [RotaryMatrix%27.eq.DotDot_RotaryMatrix](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix%27.eq.DotDot_RotaryMatrix)
  - [DotT.eq.RotaryMatrixSub](http://www.lemma.cn/lean/?module=Tensor.DotT.eq.RotaryMatrixSub)
  - [DotTInterleave.eq.Eye](http://www.lemma.cn/lean/?module=Tensor.DotTInterleave.eq.Eye)
  - [Dot_TInterleave.eq.Eye](http://www.lemma.cn/lean/?module=Tensor.Dot_TInterleave.eq.Eye)

图 1. 标题 RoPE 引理的 import 图。

# 10 讨论与限度

**检验了什么，没检验什么。** 我们认证的是张量相等，不是近似质量、长度外推，也不是 RoPE 与训练权重的相互作用。定理 8.4 对每一 \(Q,K,V\) 与每一线性 \(\theta\) 都是恒等式；它不说训练模型在推理时以某种特定方式使用相对矩阵，也不说注意力随距离衰减[[9]](https://arxiv.org/abs/2410.06205)。

**布局。** 两种配对都形式化了。`rotaryMatrix` 是 Hugging Face 对半矩阵；`rotaryMatrix'` 是苏剑林等的交错矩阵。定理 4.4 即早先草稿里未写出的置换引理。Kernel 实现（定理 5.1）与内积配对（定理 8.1）写在 Hugging Face 布局上，那是 `rotate_half` 实现的映射。RoFormer 布局上匹配的矩阵恒等式是定理 7.2。

**频率。** 定义 8.2 对引理 8.3 充分，且严格弱于古典几何表。它并非必要：任何满足 \(\theta_{k}-\theta_{t}\equiv\theta_{k-t}\pmod{2\pi}\) 的 \(\theta\) 给出同一 \(\mathrm{R}\)。

**二维与多模态 RoPE。** 轴向或多轴旋转嵌入在若干下标流上复用定义 4.1。加法与正交定理对每一流原样适用；相对下标引理需要每轴一条线性假设。包装留给后文。

**标量内积的类型。** 一维 `@` 展开为形状 \(\mathrm{matmul\_shape}\,[d]\,[d]\) 的张量，并非定义上的 \(\operatorname{Tensor}\,\mathbb{R}\,[]\)。Lean 陈述因此把这些标量包在 `id (α := Tensor ℝ [])` 里。这是库的 elaboration 事实，不是数学假设。

# 11 结语

一维 RoPE 的代数骨架，是关于平面旋转块矩阵的少数几条恒等式，布局可以是 Hugging Face 对半，也可以是苏剑林等的交错。我们在 Lean 4 中陈述了这两种矩阵，证明它们被固定的奇偶聚集共轭，并在实现所乘的 Hugging Face 矩阵上，证明了 kernel 求值、自由角的正交与加法群律、RoFormer 配对，以及线性频率假设下 softmax 注意力的相对偏移形式。引言中点名的模块即该发展的公开接口。

# 参考文献

与 `main.tex` 参考文献表一致（arXiv 接收后在此补充 PDF 链接）。勿链到仓库里的 `main.pdf`。

[1] math-proof. lemma: machine-checked tensor calculus. 2026. <https://github.com/math-proof/lemma>

[2] Jianlin Su, Yu Lu, Shengfeng Pan, Murtadha Ahmed, Bo Wen, Yunfeng Liu. RoFormer: Enhanced Transformer with Rotary Position Embedding. [arXiv:2104.09864](https://arxiv.org/abs/2104.09864), 2021.

[3] Jianlin Su, Murtadha Ahmed, Yu Lu, Shengfeng Pan, Bo Wen, Yunfeng Liu. RoFormer: Enhanced Transformer with Rotary Position Embedding. *Neurocomputing* 568:127063, 2024.

[4] Hugging Face. Utilities for Rotary Embedding. 2026. <https://github.com/huggingface/transformers/blob/main/docs/source/en/internal/rope_utils.md>

[5] Ashish Vaswani et al. Attention Is All You Need. NeurIPS, volume 30, 2017. <https://arxiv.org/abs/1706.03762>

[6] Hugo Touvron et al. LLaMA: Open and Efficient Foundation Language Models. [arXiv:2302.13971](https://arxiv.org/abs/2302.13971), 2023.

[7] Haiping Liu et al. Rethinking RoPE: A Mathematical Blueprint for \(N\)-dimensional Rotary Positional Embedding. [arXiv:2504.06308](https://arxiv.org/abs/2504.06308), 2025.

[8] Yifan Zhang et al. Group Representational Position Encoding. [arXiv:2512.07805](https://arxiv.org/abs/2512.07805), 2025.

[9] Federico Barbero et al. Round and Round We Go! What makes Rotary Positional Encodings useful? ICLR, 2025. [arXiv:2410.06205](https://arxiv.org/abs/2410.06205).

[10] Bowen Peng, Jeffrey Quesnelle, Honglu Fan, Enrico Shippole. YaRN: Efficient Context Window Extension of Large Language Models. [arXiv:2309.00071](https://arxiv.org/abs/2309.00071), 2023.

[11] Peter Shaw, Jakob Uszkoreit, Ashish Vaswani. Self-Attention with Relative Position Representations. NAACL-HLT, 2018. <https://aclanthology.org/N18-2074/>

[12] Ofir Press, Noah A. Smith, Mike Lewis. Train Short, Test Long: Attention with Linear Biases Enables Input Length Extrapolation. ICLR, 2022. [arXiv:2108.12409](https://arxiv.org/abs/2108.12409).

[13] Leonardo de Moura, Sebastian Ullrich. The Lean 4 Theorem Prover and Programming Language. CADE 28, 2021.

[14] The mathlib Community. The Lean Mathematical Library. CPP, 2020.

[15] Mathlib community. The Lean mathematical library. 2026. <https://leanprover-community.github.io/mathlib4_docs/>
