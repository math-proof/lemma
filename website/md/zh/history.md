# 符号推理与机器证明：项目沿革

<br>

## 2008 — 以符号计算为起点的公理化证明环境

2008 年起，作者在学习 C++ 的过程中开始一项长期工作：构建**公理化、可机械检验**的数学证明工具，用以辅助复杂数学推理，并探索逐步自动化的可能。项目主要在业余时间推进；初期实现采用 C++，基于德国开源符号计算库 [GiNaC](https://www.ginac.de/)，在半机械化推导中依托符号演算展开。

受当时编程条件所限，作者以 C/C++ 作为首要实现语言。C++ 的使用对后续代码风格影响深远，若干设计仍可见 C++ 痕迹，例如：

- 重载输出运算符风格的等式打印：`Eq << Equal(a, b)`（类比 `cout << "Hello World";`）
- LaTeX 输出中 lambda 抽象的书写：`Lamda[k] (h[k])`，形式接近 C++ lambda `[k]{return h[k];}`
- 对数学对象的操作沿用 `this` 指针式写法，如：`Eq << Eq[-1].this.rhs.simplify()`

## 2016 — 开源生态与「证明即程序」

2016 年前后，作者系统接触多种开源符号计算与证明辅助资源，包括 [SymPy](https://www.sympy.org/en/index.html) 及其 C++ 子项目 [SymEngine](https://github.com/symengine/symengine)、Common Lisp 系统 [Maxima](http://maxima.sourceforge.net)、集成环境 [SageMath](https://www.sagemath.org/)（整合 Maxima、[Maple](https://www.maplesoft.com/products/Maple/)、Mathematica、[MATLAB](https://www.mathworks.com/products/matlab.html)、SymPy 等），以及定理证明博物馆 [Theorem Prover Museum](https://theoremprover-museum.github.io/)、[证明助手](https://en.wikipedia.org/wiki/Proof_assistant)与[交互式证明系统](https://en.wikipedia.org/wiki/Interactive_proof_system)相关文献。

数年的阅读与实践使 [Curry–Howard 对应](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence)（「证明即程序」）成为后续架构的思想基础。与此同时，Python 在算法研究与机器学习领域迅速普及：开发效率显著高于 C++（尽管运行时性能通常不及 C++），语法亦较接近数学表述。作者据此将工程逐步**改写为 Python 实现**。

## 2018 — lemma.cn 与开放定理库

2018 年，作者建立网站 [lemma.cn](../axiom)，用于公开本项目的公理化半机械化证明工具与定理库。预期通过开源社区协作，持续扩展已形式化数学定理的覆盖范围；在定理库规模足够大时，可为基于学习的方法提供训练与评测数据，但完整的形式化数学体系仍需长期、集体的努力。

## 2021 — 符号推理与神经网络的结合（Inter-GPS）

2021 年，Lupantech 等公开了基于 Transformer 的几何题自动求解框架 **Inter-GPS**，将形式化表述、大规模数据与序列模型相结合，并嵌入符号推理步骤。该工作为「通用数学题机器求解」提供了可参照的路径：以形式语言精确表述问题，构建训练数据，用序列到序列模型预测所需定理调用序列，再与符号算法协同完成推导。

- 项目主页：<https://lupantech.github.io/inter-gps/>
- 代码：<https://github.com/lupantech/InterGPS>
- 论文：<https://arxiv.org/pdf/2105.04165.pdf>
- 中文介绍：<https://mp.weixin.qq.com/s/ZFpVpi7BsJME6uXi_2IcrQ>

## 2023 — 过程监督与形式化推理数据（OpenAI）

2023 年，OpenAI 发布约 **80 万**条面向数学推理的过程监督相关数据，用于改进逐步推导的质量评估：

- <https://openai.com/research/improving-mathematical-reasoning-with-process-supervision>
- 论文：<https://arxiv.org/abs/2305.20050>

同期，作者曾设想一种形式化的「数学 GPT」路线，要点包括：（1）**形式逻辑层**——以 Python（及后续 Lean 等形式语言）承载推理，自然语言仅作解释性输出；（2）**奖励模型**——以解释器执行结果（如 LaTeX 表达式）等指标引导推导朝向可证方向；（3）**强化学习**——由生成模型产出可执行代码，经解释器与奖励信号迭代优化。该设想与当前 **LLM 编程智能体 + 形式化核检验** 的人机协同路线一脉相承，但自动证明的最终可信度仍须依赖形式化检查，而非模型输出本身。

## 2024 — Lean 4 形式化内核与双轨仓库

2024 年起，核心定理库迁移至基于依赖类型论的 [Lean 4](https://lean-lang.org/) 证明助手（GitHub [math-proof/lemma](https://github.com/math-proof/lemma) 的 `main` 分支）；[SymPy](https://www.sympy.org/en/index.html) 交互式探索与 `apply`/`prove` 工作流仍保留于 `master` 分支，形成「形式化核检验 + 符号交互探索」双轨。经 Lean 4 核检查的定理约 **5000** 条、源码约 **10 万**行，覆盖 `Tensor` 演算、实分析与算法性质等形式化表述。网站 [lemma.cn](../index.php) 提供定理检索（`index.php?q=…`）、callee/caller 依赖视图及 Lean 源码与 LaTeX 的在线呈现。

## 2025 — 研究路线图、智能体协同与算法形式化

2025 年前后，项目发布[研究路线图](../endeavour)（`endeavour.md`）：阶段 2 明确 **100 万**量级定理库目标（Lean 生态 [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) 已率先达到 **10 万**量级）；阶段 3 将 **LLM 编程智能体**（coding agent）的人机协同证明列为当前实践方向，与 Cursor Agent、LeanDojo 等仓库感知 + 工具调用流程对齐。算法—数学交叉方面，GPT 自回归解码中 **KV cache** 的增量注意力恒等式已先后以 SymPy 与 Lean 4 形式化（详见 [KV cache 说明](../arxiv/kv_cache/main.md)；arXiv PDF 待发布），体现「生产级算法语义 → 可机器检验引理」的路径。
