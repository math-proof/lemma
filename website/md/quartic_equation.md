# Fully Radical Solution of the Quartic Equation over \(\mathbb C\)

The same lemma is published on [lemma.cn](http://www.lemma.cn/) as two public visualizations that share the module path
`Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0`:

- **SymPy version** (interactive Python / symbolic exploration):
  [http://www.lemma.cn/py/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0](http://www.lemma.cn/py/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0)
- **Lean 4 version** (machine-checked dependent type theory):
  [http://www.lemma.cn/lean/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0](http://www.lemma.cn/lean/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0)

The [SymPy page](http://www.lemma.cn/py/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0) renders the original `apply` / `prove` statement as an interactive theorem document. The [Lean 4 page](http://www.lemma.cn/lean/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0) renders the `@[main]` lemma with given/imply blocks, nested `let` binders, and the four-fold conjunction of radical expressions. Both are the public faces of this result; the present note describes the mathematics that those pages display.

## Technical Field

The present disclosure belongs to formalized computer algebra and complex analysis: closed-form roots of a univariate polynomial of degree four over the field of complex numbers, expressed by nested principal square roots and cube roots.

It concerns a complete Ferrari–Cardano formula in which every auxiliary quantity is defined by principal functions \(\sqrt{\,\cdot\,}\) and \(z^{1/3}\), together with an integer branch index assembled from the principal argument \(\operatorname{arg}\) and the ceiling function. The formula is stated twice in public: first as an interactive SymPy lemma on [lemma.cn/py](http://www.lemma.cn/py/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0), then as a Lean 4 lemma on [lemma.cn/lean](http://www.lemma.cn/lean/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0), using Mathlib’s `Complex.sqrt` and `cpow`. It is a closed-form identity, not a numerical solver.

## Background

Ferrari’s method (16th century) reduces a general quartic to a depressed quartic \(z^4+\alpha z^2+\beta z+\gamma=0\), then to a cubic resolvent and two quadratics. Cardano’s formula then solves that cubic by cube roots. Over \(\mathbb C\) the algebraic identities are classical; what is not classical is to write them as a total function of the coefficients when square roots and cube roots are the *principal* branches.

On \(\mathbb C\), Mathlib’s \(\sqrt{z}\) and \(z^{1/3}\) are defined by the principal logarithm (argument in \((-\pi,\pi]\)). They satisfy
\[
(\sqrt{z})^2=z,\qquad \bigl(z^{1/3}\bigr)^3=z
\]
for every \(z\), but they do **not** satisfy
\[
\sqrt{z}\sqrt{w}=\sqrt{zw},\qquad z^{1/3}w^{1/3}=(zw)^{1/3}
\]
in general. Cardano’s pairing \(3AB=-p\) therefore fails if one simply inserts two independent principal cube roots. Any fully radical formula over \(\mathbb C\) must name the missing cube root of unity explicitly.

Public formalizations stop short of that closed form.

- **Mathlib 4** (`Archive.Wiedijk100Theorems.SolutionOfCubicQuartic`, PR #18290, Thomas Zhu, 2024) proves Ferrari over an arbitrary field \(K\) of characteristic not two. Square roots appear as hypotheses \(t^2=\cdots\), \(v^2=\cdots\), and the resolvent root \(u\) is an extra datum. The comment on `quartic_eq_zero_iff` states that an explicit Cardano expression for \(u\) “would be too long.” The theorem is therefore not a map \(\mathbb C^5\to\mathbb C^4\) in principal radicals, and it is not specific to \(\mathbb C\).
- **Dyson–Ahrens–Emmenegger** (Lean 3, [arXiv:2201.00255](https://arxiv.org/abs/2201.00255), 2022) work in a field equipped with *some* square-root and cube-root operations. The functions are axioms, not Mathlib’s principal branches; the product identity for cube roots is deliberately not assumed. Instantiating the typeclass with \(\mathbb C\) does not prove the principal-branch formula.
- **Coq** (the development compared in that paper, §7.1) is specific to \(\mathbb C\) and uses De Moivre \(n\)th roots. That is a complex-domain radical solution, but it is not a Lean 4 lemma, and it does not use Mathlib’s principal \(\sqrt{\,\cdot\,}\) / `cpow` together with an `arg`/`⌈·⌉` selector.
- **Isabelle/HOL** `Cubic_Quartic` and the HOL Light entry on Wiedijk’s list are algebraic in the same sense as Mathlib: roots are assumed, not constructed by principal functions.

This library already has a companion cubic lemma
[Algebra.And_Imp_Or_EqS.of.Add.eq.Zero.cubic](http://www.lemma.cn/lean/?module=Algebra.And_Imp_Or_EqS.of.Add.eq.Zero.cubic)
that solves \(ax^3+bx^2+cx+d=0\) over \(\mathbb C\) by principal radicals and the same integer
\[
D=\Bigl\lceil\frac{3\operatorname{arg}(-p/3)}{2\pi}-\frac12\Bigr\rceil
-\Bigl\lceil\frac{3\operatorname{arg}(AB)}{2\pi}-\frac12\Bigr\rceil.
\]
The quartic lemma’s distinct contribution is to finish Ferrari on that calculus: the cubic resolvent is not left as a hypothesis; it is expanded by Cardano, one valid resolvent root \(y\) is selected by \(D\bmod 3\), and the four quartic roots are nested principal square roots of that \(y\). Among public Lean 4 sources, this is the first fully expanded principal-radical quartic over \(\mathbb C\). It is not the first quartic in Lean 4, and it is not the first Complex radical quartic in any proof assistant.

The statement is public in two visualizations on lemma.cn, under the same module name. The [SymPy page](http://www.lemma.cn/py/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0) is the original interactive form (created 2018-11-29): a Python `apply` that returns four implications, proved by reducing to the monic quartic and calling the library’s depressed solver. The [Lean 4 page](http://www.lemma.cn/lean/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0) is the machine-checked form of that same given/imply skeleton, with every `let` binder and every principal radical visible in the rendered lemma. Mathlib, Coq, and Isabelle do not publish this fully expanded \(\mathbb C\) formula as a browsable theorem page of that kind.

## Summary

Let \(a,b,c,d,e,x\in\mathbb C\) with \(a\neq 0\) and
\[
a x^4+b x^3+c x^2+d x+e=0.
\]
Write \(a'=b/a\), \(b'=c/a\), \(c'=d/a\), \(d'=e/a\), and
\[
\begin{align*}
\alpha&=b'-3a'^2/8,\\
\beta&=a'^3/8+c'-a'b'/2,\\
\gamma&=a'^2 b'/16+d'-3a'^4/256-a'c'/4.
\end{align*}
\]
Then \(z=x+a'/4\) satisfies the depressed equation \(z^4+\alpha z^2+\beta z+\gamma=0\), and \(x\) is one of four explicit nested radicals, in two regimes.

**Biquadratic regime** \(\beta=0\). With \(\Delta=\alpha^2-4\gamma\),
\[
x=\pm\sqrt{\pm\sqrt{\Delta}/2-\alpha/2}-a'/4
\]
(four independent choices of the two signs).

**Ferrari regime** \(\beta\neq 0\). Form Cardano quantities of the resolvent,
\[
\begin{align*}
p&=-\gamma-\alpha^2/12,\\
q&=-\alpha^3/108+\alpha\gamma/3-\beta^2/8,\\
\delta_c&=4p^3/27+q^2,\\
A_c&=\bigl(\sqrt{\delta_c}/2-q/2\bigr)^{1/3},\quad
B_c=\bigl(-\sqrt{\delta_c}/2-q/2\bigr)^{1/3},
\end{align*}
\]
and the same \(p,q\) written from the intermediate coefficients \(a_r=-\alpha/2\), \(b_r=-\gamma\), \(c_r=-\beta^2/8+\alpha\gamma/2\) as in the lemma. Let
\[
D=\Bigl\lceil\frac{3\operatorname{arg}(-p/3)}{2\pi}-\frac12\Bigr\rceil
-\Bigl\lceil\frac{3\operatorname{arg}(A_c B_c)}{2\pi}-\frac12\Bigr\rceil,
\]
\(\omega=-1/2+i\sqrt{3}/2\), and let \(A,B\) be the principal cube roots of the scaled Cardano pair \((U,V)\) (equivalently \(A=2A_c\), \(B=2B_c\)). Set
\[
y=
\begin{cases}
A+B & \text{if }D=0,\\
A\omega+B & \text{if }D\equiv 1\pmod{3},\\
A\,\overline{\omega}+B & \text{if }D\equiv 2\pmod{3},
\end{cases}
\qquad
y_0=-2\alpha/3+y,\qquad
y_1=4\alpha/3+y.
\]
Then
\[
\begin{align*}
x&=\frac{\sqrt{2\beta/\sqrt{y_0}-y_1}}{2}-\frac{\sqrt{y_0}}{2}-\frac{a'}{4}\\
&\quad\text{or}\quad
-\frac{\sqrt{2\beta/\sqrt{y_0}-y_1}}{2}-\frac{\sqrt{y_0}}{2}-\frac{a'}{4}\\
&\quad\text{or}\quad
\frac{\sqrt{-2\beta/\sqrt{y_0}-y_1}}{2}+\frac{\sqrt{y_0}}{2}-\frac{a'}{4}\\
&\quad\text{or}\quad
-\frac{\sqrt{-2\beta/\sqrt{y_0}-y_1}}{2}+\frac{\sqrt{y_0}}{2}-\frac{a'}{4}.
\end{align*}
\]

The lemma is a four-fold conjunction of implications, one for \(\beta=0\) and one for each residue of \(D\) modulo 3. It does not claim that every combination of nested radicals is a root for a wrong branch; it claims that a genuine root \(x\) equals one of the four expressions once the correct branch is selected.

## Brief Description of the Drawings

FIG. 0 comprises the two public lemma.cn visualizations of the finished statement, under one module name:

- SymPy: [http://www.lemma.cn/py/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0](http://www.lemma.cn/py/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0)
- Lean 4: [http://www.lemma.cn/lean/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0](http://www.lemma.cn/lean/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0)

FIG. 1 is the reduction used in the main theorem: divide by the leading coefficient, depress by \(z=x+a'/4\), then split on \(\beta=0\) versus \(\beta\neq 0\).

FIG. 2 is the import graph of major sub-lemmas actually used to prove the main theorem. Private helpers in the same file are drawn in parentheses. Links in FIG. 2 point to the Lean 4 pages; the SymPy counterpart of each module is the same path under `http://www.lemma.cn/py/?module=…`.

FIG. 3 is the cube-root branch selector \(D\), shared in design with the library’s cubic formula, and applied here only to the Ferrari resolvent (one root \(y\), not three Cardano triples).

**FIG. 0 — public visualizations**

The [SymPy page](http://www.lemma.cn/py/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0) is the rendering: given `a ≠ 0` and `a x^4 + b x^3 + c x^2 + d x + e = 0`, it displays four implications (`β = 0`, `β ≠ 0 ∧ D = 0`, `D % 3 = 1`, `D % 3 = 2`) with nested radicals as an interactive theorem document. The [Lean 4 page](http://www.lemma.cn/lean/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0) is the rendering of the same skeleton: `@[main] private lemma main` with `{x a b c d e : ℂ}`, the `let` chain `a', b', α, β, γ, δ, U, V, A, B, …, D, ω`, and the four-fold `∧` of radical disjunctions. Those two URLs are the public drawings of the lemma.

**FIG. 1 — reduction**

\[
\begin{array}{c}
a x^{4}+b x^{3}+c x^{2}+d x+e=0,\quad a\neq 0 \\[0.8em]
\Big\downarrow\ \scriptstyle a'=\dfrac{b}{a},\; b'=\dfrac{c}{a},\; c'=\dfrac{d}{a},\; d'=\dfrac{e}{a} \\[0.8em]
x^{4}+a' x^{3}+b' x^{2}+c' x+d'=0 \\[0.8em]
\Big\downarrow\ \scriptstyle z=x+\dfrac{a'}{4} \\[0.8em]
z^{4}+\alpha z^{2}+\beta z+\gamma=0 \\[0.35em]
\scriptstyle
\alpha=b'-\dfrac{3a'^{2}}{8},\quad
\beta=\dfrac{a'^{3}}{8}+c'-\dfrac{a'b'}{2},\quad
\gamma=\dfrac{a'^{2}b'}{16}+d'-\dfrac{3a'^{4}}{256}-\dfrac{a'c'}{4}
\\[1.2em]
\begin{array}{c@{\qquad}c}
\beta=0 & \beta\neq 0 \\[0.55em]
\Big\downarrow & \Big\downarrow \\[0.55em]
\Delta=\alpha^{2}-4\gamma &
y=
\begin{cases}
A+B & D=0 \\
A\omega+B & D\equiv 1\pmod{3} \\
A\,\overline{\omega}+B & D\equiv 2\pmod{3}
\end{cases}
\\[2.4em]
x=\pm\sqrt{\pm\dfrac{\sqrt{\Delta}}{2}-\dfrac{\alpha}{2}}-\dfrac{a'}{4}
&
\begin{array}{c}
y_{0}=-\dfrac{2\alpha}{3}+y,\quad y_{1}=\dfrac{4\alpha}{3}+y \\[0.6em]
x=\dfrac{\pm\sqrt{\pm\dfrac{2\beta}{\sqrt{y_{0}}}-y_{1}}}{2}\pm\dfrac{\sqrt{y_{0}}}{2}-\dfrac{a'}{4}
\end{array}
\end{array}
\\[1.4em]
x=z-\dfrac{a'}{4}
\end{array}
\]

**FIG. 2 — lemma dependencies of the main theorem**

- `Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0` ([SymPy](http://www.lemma.cn/py/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0) / [Lean 4](http://www.lemma.cn/lean/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0))
  - [Algebra.Or_Eq.of.Add.eq.Zero.biquadratic](http://www.lemma.cn/lean/?module=Algebra.Or_Eq.of.Add.eq.Zero.biquadratic) — case \(\beta=0\)
    - [Algebra.And_Imp_Or_EqS_Div.of.Add.eq.Zero.quadratic](http://www.lemma.cn/lean/?module=Algebra.And_Imp_Or_EqS_Div.of.Add.eq.Zero.quadratic) — quadratic in \(x^2\)
      - [Complex.Imp_Eq_0.Imp_Eq_DivNeg.Imp_OrEqS_Div_Mul2.of.Eq0AddAddMul_Square](http://www.lemma.cn/lean/?module=Complex.Imp_Eq_0.Imp_Eq_DivNeg.Imp_OrEqS_Div_Mul2.of.Eq0AddAddMul_Square)
        - [Complex.OrEqS_Div_Mul2.of.Eq0AddAddMul_Square.Ne_0](http://www.lemma.cn/lean/?module=Complex.OrEqS_Div_Mul2.of.Eq0AddAddMul_Square.Ne_0)
        - [Rat.ImpEq.ImpNe.of.AddMul.eq.Zero](http://www.lemma.cn/lean/?module=Rat.ImpEq.ImpNe.of.AddMul.eq.Zero)
    - [Complex.Or_Eq_NegSqrt.of.EqSquare](http://www.lemma.cn/lean/?module=Complex.Or_Eq_NegSqrt.of.EqSquare) — \(x^2=c\Rightarrow x=\sqrt{c}\lor x=-\sqrt{c}\)
      - [Complex.EqSquareSqrt](http://www.lemma.cn/lean/?module=Complex.EqSquareSqrt) — \((\sqrt{z})^2=z\)
      - [Real.OrEqS.of.Square](http://www.lemma.cn/lean/?module=Real.OrEqS.of.Square)
  - [Algebra.And.Imp.of.Add.eq.Zero.Ne_0.quartic.depressed](http://www.lemma.cn/lean/?module=Algebra.And.Imp.of.Add.eq.Zero.Ne_0.quartic.depressed) — case \(\beta\neq 0\)
    - (`ferrari_roots`) — given a resolvent root \(y_0\), factor into two quadratics
      - [Complex.EqSquareSqrt](http://www.lemma.cn/lean/?module=Complex.EqSquareSqrt)
      - [Complex.Or_Eq_NegSqrt.of.EqSquare](http://www.lemma.cn/lean/?module=Complex.Or_Eq_NegSqrt.of.EqSquare)
    - [Algebra.Eq.of.Eq_Pow.cubic_root.omega](http://www.lemma.cn/lean/?module=Algebra.Eq.of.Eq_Pow.cubic_root.omega) — \(A^3=B^3\Rightarrow A=B\,\omega^d\) with \(d\) from \(\operatorname{arg}\) and \(\lceil\cdot\rceil\)
      - [Algebra.Arg.Pow.eq.Add](http://www.lemma.cn/lean/?module=Algebra.Arg.Pow.eq.Add) — \(\operatorname{arg}(z^n)=n\operatorname{arg} z-2\pi\lceil n\operatorname{arg} z/(2\pi)-1/2\rceil\)
        - [Algebra.Expr.eq.MulAbs_ExpMulIArg](http://www.lemma.cn/lean/?module=Algebra.Expr.eq.MulAbs_ExpMulIArg) — polar form \(z=\|z\|e^{i\operatorname{arg} z}\)
        - [Algebra.EqArg.of.Gt_0](http://www.lemma.cn/lean/?module=Algebra.EqArg.of.Gt_0)
        - [Complex.ArgExpMulI.eq.Sub_Mul_Ceil](http://www.lemma.cn/lean/?module=Complex.ArgExpMulI.eq.Sub_Mul_Ceil) — \(\operatorname{arg}(e^{ix})=x-2\pi\lceil x/(2\pi)-1/2\rceil\)
          - [Int.Floor.eq.NegCeilNeg](http://www.lemma.cn/lean/?module=Int.Floor.eq.NegCeilNeg)
      - [Algebra.Expr.eq.MulAbs_ExpMulIArg](http://www.lemma.cn/lean/?module=Algebra.Expr.eq.MulAbs_ExpMulIArg)

Related lemmas in the same family, **not** imported by the main theorem: the \(\beta=0\)-only depressed statement
[Algebra.And.Imp.of.Add.eq.Zero.quartic.depressed](http://www.lemma.cn/lean/?module=Algebra.And.Imp.of.Add.eq.Zero.quartic.depressed)
and the monic offset
[Algebra.And.Imp.of.Add.eq.Zero.quartic.one_leaded](http://www.lemma.cn/lean/?module=Algebra.And.Imp.of.Add.eq.Zero.quartic.one_leaded).
The cubic formula
[Algebra.Or.Eq.of.Add.eq.Zero.Eq_Ceil.cubic](http://www.lemma.cn/lean/?module=Algebra.Or.Eq.of.Add.eq.Zero.Eq_Ceil.cubic)
uses the same \(D\) selector; the quartic proof calls `cubic_root.omega` directly, because Ferrari needs one resolvent root rather than the three Cardano combinations.

**FIG. 3 — branch integer \(D\)**

From \(A^3=B^3\) one has \(A=B\,\omega^d\) with
\[
d=\Bigl\lceil\frac{3\operatorname{arg} A}{2\pi}-\frac12\Bigr\rceil
-\Bigl\lceil\frac{3\operatorname{arg} B}{2\pi}-\frac12\Bigr\rceil.
\]
Applied to \(A_c B_c\) and \(-p/3\), this is the \(D\) of the main theorem, and \(\omega^{-D}\) restores \(3AB=-4p\) after the scaling \(A=2A_c\), \(B=2B_c\). Multiplying only \(A\) by \(1\), \(\omega\), or \(\overline{\omega}\) according to \(D\bmod 3\) produces a legal Ferrari parameter \(y\).

## Detailed Description

### 1. Principal radicals

Throughout, \(\sqrt{\,\cdot\,}\) is Mathlib `Complex.sqrt` and \(z^{1/3}\) is `cpow` with exponent \((3:\mathbb C)^{-1}\). Both are total functions \(\mathbb C\to\mathbb C\). The identity \((\sqrt{z})^2=z\) is
[Complex.EqSquareSqrt](http://www.lemma.cn/lean/?module=Complex.EqSquareSqrt).
If \(x^2=c\), then \(x=\sqrt{c}\) or \(x=-\sqrt{c}\) by
[Complex.Or_Eq_NegSqrt.of.EqSquare](http://www.lemma.cn/lean/?module=Complex.Or_Eq_NegSqrt.of.EqSquare).
Cube roots of unity are written
\[
\omega=-\tfrac12+i\tfrac{\sqrt{3}}{2},\qquad \overline{\omega}=\omega^2,\qquad \omega^3=1.
\]
The polar form \(z=\|z\|e^{i\operatorname{arg} z}\) is
[Algebra.Expr.eq.MulAbs_ExpMulIArg](http://www.lemma.cn/lean/?module=Algebra.Expr.eq.MulAbs_ExpMulIArg).
The reduction of \(\operatorname{arg}(e^{ix})\) into \((-\pi,\pi]\) by a ceiling is
[Complex.ArgExpMulI.eq.Sub_Mul_Ceil](http://www.lemma.cn/lean/?module=Complex.ArgExpMulI.eq.Sub_Mul_Ceil),
which yields the power rule
[Algebra.Arg.Pow.eq.Add](http://www.lemma.cn/lean/?module=Algebra.Arg.Pow.eq.Add)
and then the cube-root comparison
[Algebra.Eq.of.Eq_Pow.cubic_root.omega](http://www.lemma.cn/lean/?module=Algebra.Eq.of.Eq_Pow.cubic_root.omega):
if \(A^3=B^3\), then \(A=B\,\omega^d\) for the integer \(d\) of FIG. 3.

### 2. From a general quartic to a depressed quartic

Assume \(a\neq 0\) and \(a x^4+b x^3+c x^2+d x+e=0\). Division by \(a\) produces the monic equation
\[
x^4+a'x^3+b'x^2+c'x+d'=0.
\]
The translation \(z=x+a'/4\) cancels the cubic term. Expanding and collecting coefficients gives the depressed quartic
\[
z^4+\alpha z^2+\beta z+\gamma=0
\]
with \(\alpha,\beta,\gamma\) as in the Summary. The main file performs this expansion by `ring`; the four nested-radical expressions for \(z\) are then shifted back by \(-a'/4\).

### 3. Biquadratic case \(\beta=0\)

If \(\beta=0\), the depressed equation is \(z^4+\alpha z^2+\gamma=0\), a quadratic in \(z^2\). Lemma
[Algebra.And_Imp_Or_EqS_Div.of.Add.eq.Zero.quadratic](http://www.lemma.cn/lean/?module=Algebra.And_Imp_Or_EqS_Div.of.Add.eq.Zero.quadratic)
gives
\[
z^2=\frac{-\alpha\pm\sqrt{\alpha^2-4\gamma}}{2}=\pm\frac{\sqrt{\Delta}}{2}-\frac{\alpha}{2},\qquad \Delta=\alpha^2-4\gamma.
\]
Each quadratic \(z^2=c\) splits by the principal square-root alternative, which is
[Algebra.Or_Eq.of.Add.eq.Zero.biquadratic](http://www.lemma.cn/lean/?module=Algebra.Or_Eq.of.Add.eq.Zero.biquadratic).
Translating \(x=z-a'/4\) is the first conjunct of the main theorem.

### 4. Ferrari factorization when \(\beta\neq 0\)

Let \(y_0\in\mathbb C\) be any root of the cubic resolvent
\[
y_0^3+2\alpha y_0^2+(\alpha^2-4\gamma)y_0-\beta^2=0,
\]
and set \(y_1=y_0+2\alpha\). The private lemma `ferrari_roots` proves that \(y_0\neq 0\) (else \(\beta=0\)), that \((\sqrt{y_0})^2=y_0\), and that with \(Y=(y_0+\alpha)/2\) one has the completing-the-square identity
\[
(z^2+Y)^2-\bigl(\sqrt{y_0}\,z-\beta/(2\sqrt{y_0})\bigr)^2
=z^4+\alpha z^2+\beta z+\gamma.
\]
The left-hand side is a difference of squares, hence a product of two quadratics. Each quadratic is solved by completing the square again and applying `Or_Eq_NegSqrt`, which produces the four expressions
\[
\begin{align*}
z&=\frac{\sqrt{2\beta/\sqrt{y_0}-y_1}}{2}-\frac{\sqrt{y_0}}{2},&
z&=-\frac{\sqrt{2\beta/\sqrt{y_0}-y_1}}{2}-\frac{\sqrt{y_0}}{2},\\
z&=\frac{\sqrt{-2\beta/\sqrt{y_0}-y_1}}{2}+\frac{\sqrt{y_0}}{2},&
z&=-\frac{\sqrt{-2\beta/\sqrt{y_0}-y_1}}{2}+\frac{\sqrt{y_0}}{2}.
\end{align*}
\]
This step still treats \(y_0\) as given. The rest of the proof constructs \(y_0\) from principal radicals.

### 5. Cardano data of the resolvent

Depress the resolvent by the substitution associated with coefficients
\[
a_r=-\alpha/2,\qquad b_r=-\gamma,\qquad c_r=-\beta^2/8+\alpha\gamma/2.
\]
The depressed Cardano parameters are
\[
p=b_r-a_r^2/3,\qquad
q=2a_r^3/27-a_r b_r/3+c_r,
\]
and the usual discriminant \(\delta_c=4p^3/27+q^2\). Principal cube roots
\[
A_c=\bigl(\sqrt{\delta_c}/2-q/2\bigr)^{1/3},\qquad
B_c=\bigl(-\sqrt{\delta_c}/2-q/2\bigr)^{1/3}
\]
satisfy \((A_c B_c)^3=(-p/3)^3\). Independently, the lemma writes a scaled Cardano pair
\[
\begin{align*}
\delta&=-(\alpha^2/3+4\gamma)^3/27+(-\alpha^3/27+4\alpha\gamma/3-\beta^2/2)^2,\\
U&=\alpha^3/27-4\alpha\gamma/3+\beta^2/2+\sqrt{\delta},\\
V&=\alpha^3/27-4\alpha\gamma/3+\beta^2/2-\sqrt{\delta},\\
A&=U^{1/3},\qquad B=V^{1/3}.
\end{align*}
\]
A direct calculation gives \(\delta=16\delta_c\), \(\sqrt{\delta}=4\sqrt{\delta_c}\) (using \((16z)^{1/2}=4 z^{1/2}\) for the principal branch, which holds because \(16>0\)), and
\[
U=8\bigl(\sqrt{\delta_c}/2-q/2\bigr),\qquad
V=8\bigl(-\sqrt{\delta_c}/2-q/2\bigr).
\]
Positive real scaling of cube roots then yields \(A=2A_c\) and \(B=2B_c\). These identities connect the expanded Ferrari radicals in the theorem statement to the normalized cubic Cardano pair \((A_c,B_c)\) on which the argument computation is performed.

### 6. Restoring the product identity \(3A'B=-4p\)

Because \((A_c B_c)^3=(-p/3)^3\), lemma `cubic_root.omega` supplies
\[
A_c B_c=(-p/3)\,\omega^{-D}
\]
with the integer \(D\) of the Summary. If \(D=0\), then \(A_c B_c=-p/3\), hence
\[
3AB=3\cdot 4\cdot A_c B_c=-4p.
\]
If \(D\equiv 1\pmod{3}\), replace \(A\) by \(A'=A\omega\). Then \((A')^3=A^3=U\) still, while
\[
\omega^{-D}\cdot\omega=\omega^{1-D}=1
\]
because \(1-D\equiv 0\pmod{3}\) and \(\omega^3=1\). If \(D\equiv 2\pmod{3}\), replace \(A\) by \(A'=A\overline{\omega}=A\omega^2\); then \(\omega^{-D}\omega^2=1\). In every case one obtains a pair \((A',B)\) with
\[
(A')^3+B^3=U+V=-8q,\qquad 3A'B=-4p,
\]
so \(y=A'+B\) satisfies the depressed cubic \(y^3+4p y+8q=0\). Shifting
\[
y_0=-2\alpha/3+y,\qquad y_1=4\alpha/3+y
\]
recovers a root of the Ferrari resolvent, and `ferrari_roots` applies.

Unlike the cubic formula in this library, only \(A\) is rotated. A quartic needs one legal resolvent parameter, not three Cardano roots of the original unknown.

### 7. Shape of the theorem

The statement is a conjunction of implications, not an if-and-only-if that would list roots for a mismatched branch:

1. \(\beta=0\) implies the four biquadratic expressions.
2. \(\beta\neq 0\) and \(D=0\) implies the four Ferrari expressions with \(y=A+B\).
3. \(\beta\neq 0\) and \(D\equiv 1\pmod{3}\) implies the same expressions with \(y=A\omega+B\).
4. \(\beta\neq 0\) and \(D\equiv 2\pmod{3}\) implies the same expressions with \(y=A\overline{\omega}+B\).

Each inner disjunction is exhaustive for that case: a root \(x\) of the original polynomial equals one of the four nested radicals. Principal square roots in the Ferrari step may individually vanish or repeat when the quartic has multiple roots; the disjunction still holds.

### 8. What is not claimed

The lemma does not construct roots in a general field of characteristic zero, does not avoid \(\operatorname{arg}\) and \(\lceil\cdot\rceil\), and does not prove that a randomly chosen pairing of principal cube roots is a resolvent root. It also does not replace Mathlib’s abstract Ferrari theorem: that theorem remains the right statement when one only knows that some square roots and some resolvent root exist in \(K\). The present lemma is the complementary statement on \(\mathbb C\): every coefficient tuple with \(a\neq 0\) is sent to four explicit principal-radical expressions, with the cube-root branch named by \(D\). That statement is the one visualized at
[lemma.cn/py](http://www.lemma.cn/py/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0)
and
[lemma.cn/lean](http://www.lemma.cn/lean/?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0).
