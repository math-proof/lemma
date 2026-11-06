import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Def.Analysis.SpecialFunctions.Trigonometric
import Lemma.Real.HasDerivAt_Deriv.is.DifferentiableAt
import Syntax.Analysis.Calculus.Deriv.Operators
open Real Hyperreal


/--
Nonlinear continuum wave law from soft-string \(F=ma\).

Given the continuum soft-string force balance `h_force`
\[
  T\,\partial_x\bigl(\sin(\arctan u_x)\bigr)=\mu\,u_{tt}
\]
and spatial regularity `h_ux'` (`DifferentiableAt` of \(u_x\), i.e. \(C^2\) in \(x\)),
conclude
\[
  T_{\mathrm{tension}}\,\frac{u_{xx}}{(1+u_x^2)^{3/2}}=\mu\,u_{tt}
\]
pointwise for every \(t,x\).

The older discrete free-body form of the force law was
\[
  T\bigl(\sin(\arctan u_x(x+\Delta x))-\sin(\arctan u_x(x))\bigr)
  =\mu\,\Delta x\,u_{tt}
\]
for infinitesimal \(\Delta x\to 0^+\); its continuum limit is the binder `h_force` above.

Derivation (no appeal to
[Mersenne's frequency law](?module=Hyperreal.Eq_Mul_SqrtDiv.of.All_EqMul_Deriv_SinArctan.All_Eq_MulMul_Sin_Cos)):
chain rule for \(x\mapsto\sin(\arctan u_x)\) yields
\(\partial_x(\sin(\arctan u_x))=u_{xx}/(1+u_x^2)^{3/2}\), so `h_force` rewrites to the
displayed identity. The linear wave equation
\(T_{\mathrm{tension}} u_{xx}=\mu u_{tt}\) is the special case \(u_x=0\)
(or the small-slope approximation \(|u_x|\ll 1\)).
-/
@[path]
private lemma main
  {T μ : ℝ⁺}
  {u : ℝ → ℝ → ℝ}
-- given
  (h_ux' : ∀ t x, DifferentiableAt ℝ (deriv (u t)) x)
  (h_force : ∀ (t x : ℝ),
    T * ∂[x] (∂[x] u t x).arctan.sin = μ * ∂[t, t] u t x) :
-- imply
  ∀ t x,
    (T : ℝ) * (∂[x, x] u t x) / (1 + (∂[x] u t x) ^ 2) ^ ((3 : ℝ) / 2) =
      (μ : ℝ) * ∂[t, t] u t x := by
-- proof
  intro t x
  set ux : ℝ := ∂[x] u t x
  set uxx : ℝ := ∂[x, x] u t x
  set utt : ℝ := ∂[t, t] u t x
  set g : ℝ → ℝ := fun y => Real.sin (Real.arctan (deriv (u t) y))
  set g' : ℝ := uxx / (1 + ux ^ 2) ^ ((3 : ℝ) / 2)
  have h_ux_deriv : HasDerivAt (deriv (u t)) uxx x := by
    -- DifferentiableAt ⇒ HasDerivAt f (deriv f x); uxx = ∂[x,x] u = deriv (deriv (u t)) x
    simpa [uxx] using HasDerivAt_Deriv.of.DifferentiableAt (h_ux' t x)
  have hval :
    Real.cos (Real.arctan ux) * (1 / (1 + ux ^ 2) * uxx) = g' := by
    have hpos : 0 < 1 + ux ^ 2 := by nlinarith
    simp only [g']
    rw [Real.cos_arctan, Real.sqrt_eq_rpow]
    rw [show (3 : ℝ) / 2 = (1 : ℝ) / 2 + 1 by ring]
    rw [Real.rpow_add hpos, Real.rpow_one]
    field_simp
  have hg : HasDerivAt g g' x := by
    have h :=
      (hasDerivAt_sin (Real.arctan (deriv (u t) x))).comp x
        ((hasDerivAt_arctan (deriv (u t) x)).comp x h_ux_deriv)
    have hfun : g = Real.sin ∘ Real.arctan ∘ deriv (u t) := by
      funext y; rfl
    rw [hfun]
    convert h using 1
    -- cos(arctan(u_x))*((1/(1+u_x²))*u_xx) = g'
    simpa [g', ux, uxx] using hval.symm
  have h_gsin : ∂[x] (∂[x] u t x).arctan.sin = g' := by
    -- sugar: deriv (fun y ↦ sin (arctan (deriv (fun y ↦ u t y) y))) x
    change deriv (fun y => Real.sin (Real.arctan (deriv (fun y => u t y) y))) x = g'
    have hfun : (fun y => Real.sin (Real.arctan (deriv (fun y => u t y) y))) = g := by
      funext y
      simp only [g]
    simpa [hfun] using hg.deriv
  have hforce := h_force t x
  rw [h_gsin] at hforce
  -- T * g' = μ * utt; goal is T * uxx/(…)=μ * utt
  simpa [g', ux, uxx, utt, mul_div_assoc] using hforce


-- created on 2026-11-05
