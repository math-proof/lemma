import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Def.Analysis.SpecialFunctions.Trigonometric
import Instance.Analysis.Hyperreal.Coe
import Lemma.Hyperreal.SubMapAddCoe.XEqDiv.of.HasDerivAt.InfinitesimalPos
import Lemma.Hyperreal.InfinitesimalSub.of.XEq.NotInfinite
import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt
import Lemma.Hyperreal.GtEpsilon_0
import Lemma.Hyperreal.Ne_0.of.InfinitesimalPos
import Lemma.Real.HasDerivAt_Deriv.is.DifferentiableAt
import Notation.Analysis.Real.Numbers
import Syntax.Analysis.Calculus.Deriv.Operators
import Syntax.Analysis.Real.Limits
import Initialize.Tactic.Attr.Basic
open Real Hyperreal ArchimedeanClass Filter


/--
Continuum soft-string force balance from the discrete free-body law.

The discrete free-body force law for an infinitesimal mesh step \(\Delta x\to 0^+\) is
\[
  T\bigl(\sin(\arctan u_x(x+\Delta x))-\sin(\arctan u_x(x))\bigr)
  =\mu\,\Delta x\,u_{tt}.
\]
Under spatial \(C^2\) regularity `h_ux'` (`DifferentiableAt` of \(u_x\)), the continuum
limit is the soft-string binder
\[
  T\,\partial_x\bigl(\sin(\arctan u_x)\bigr)=\mu\,u_{tt}.
\]
Proof: set \(g=\sin\circ\arctan\circ u_x\); `h_ux'` and smoothness of \(\sin,\arctan\) give
`HasDerivAt g (deriv g x) x`. Specialize the discrete law at \(\Delta x=\varepsilon>0\)
infinitesimal, divide by \(T\varepsilon\), and apply NSA microaffinity
[difference quotient \(\approx\) derivative](?module=Hyperreal.SubMapAddCoe.XEqDiv.of.HasDerivAt.InfinitesimalPos)
to identify \(\operatorname{deriv} g\,x=(\mu/T)\,u_{tt}\).
-/
@[path]
private lemma main
  {T μ : ℝ⁺}
  {u : ℝ → ℝ → ℝ}
-- given
  (h_ux' : ∀ t x, DifferentiableAt ℝ (deriv (u t)) x)
  (h_force : ∀ (t x : ℝ) (Δx : ℝ*), (h_Δx : Δx → 0⁺) →
    T * (∂[x = x + Δx] u t x).arctan.sin -
      T * (∂[x] u t x).arctan.sin =
      μ * Δx * ∂[t, t] u t x) :
-- imply
  ∀ (t x : ℝ),
    T * ∂[x] (∂[x] u t x).arctan.sin = μ * ∂[t, t] u t x := by
-- proof
  intro t x
  set g : ℝ → ℝ := fun y => Real.sin (Real.arctan (deriv (u t) y))
  set utt : ℝ := ∂[t, t] u t x
  set c : ℝ := (μ : ℝ) / (T : ℝ) * utt
  have hT : (T : ℝ) ≠ 0 := T.property.ne'
  have hε : (ε : ℝ*) → 0⁺ := ⟨epsilon_pos, archimedeanClassMk_epsilon_pos⟩
  have hε0 : (ε : ℝ*) ≠ 0 := Ne_0.of.InfinitesimalPos hε
  have hdisc := h_force t x ε hε
  have hg : HasDerivAt g (deriv g x) x := by
    refine HasDerivAt_Deriv.of.DifferentiableAt ?_
    have h_ux_deriv := HasDerivAt_Deriv.of.DifferentiableAt (h_ux' t x)
    have h :=
      (hasDerivAt_sin (Real.arctan (deriv (u t) x))).comp x
        ((hasDerivAt_arctan (deriv (u t) x)).comp x h_ux_deriv)
    have hfun : g = Real.sin ∘ Real.arctan ∘ deriv (u t) := funext fun _ => rfl
    simpa [hfun] using h.differentiableAt
  have hmicro :=
    SubMapAddCoe.XEqDiv.of.HasDerivAt.InfinitesimalPos (g := g) (g' := deriv g x) hg hε
  have hmap :
    (∂[x = x + ε] u t x).arctan.sin =
      (show ℝ* from Germ.map g ((x : ℝ*) + ε)) := by
    simp only [Hyperreal.sin, Hyperreal.arctan]
    change
      Germ.map Real.sin
        (Germ.map Real.arctan
          (Germ.map (fun y : ℝ => deriv (fun y => u t y) y) ((x : ℝ*) + ε))) =
        Germ.map g ((x : ℝ*) + ε)
    refine Germ.inductionOn ((x : ℝ*) + ε) fun d => ?_
    rw [Germ.map_coe, Germ.map_coe, Germ.map_coe, Germ.map_coe]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun n => rfl
  -- Discrete law as T * (map g − ↑(g x)) = μ * ε * ↑utt
  have hsub :
    (T : ℝ*) *
        ((show ℝ* from Germ.map g ((x : ℝ*) + ε)) - ↑(g x)) =
      (μ : ℝ*) * ε * ↑utt := by
    have h := hdisc
    rw [hmap] at h
    have hgx : g x = Real.sin (Real.arctan (deriv (fun y => u t y) x)) := by
      simp only [g]
    rw [← hgx] at h
    rwa [mul_sub]
  have hT' : (T : ℝ*) ≠ 0 := by
    norm_cast
  have hquot :
    ((show ℝ* from Germ.map g ((x : ℝ*) + ε)) - ↑(g x)) / ε = ↑c := by
    have h1 :
      ((show ℝ* from Germ.map g ((x : ℝ*) + ε)) - ↑(g x)) =
        (μ : ℝ*) * ↑utt / (T : ℝ*) * ε := calc
        _ = (T : ℝ*) *
              ((show ℝ* from Germ.map g ((x : ℝ*) + ε)) - ↑(g x)) / (T : ℝ*) := by
          field_simp [hT']
        _ = (μ : ℝ*) * ε * ↑utt / (T : ℝ*) := by
          rw [hsub]
        _ = (μ : ℝ*) * ↑utt / (T : ℝ*) * ε := by
          ring
    calc
      _ = (μ : ℝ*) * ↑utt / (T : ℝ*) * ε / ε := by
        rw [h1]
      _ = (μ : ℝ*) * ↑utt / (T : ℝ*) := by
        field_simp [hε0]
      _ = ↑c := by
        simp only [c]
        push_cast
        ring
  have hxeq : (↑c : ℝ*) ≈ ↑(deriv g x) := by
    rwa [← hquot]
  have hder_eq : deriv g x = c := by
    have hnotInf : ¬(↑c : ℝ*) → ∞ := fun h =>
      (not_lt_of_ge (archimedeanClassMk_coe_nonneg c)) h
    have hinf : ((↑c : ℝ*) - ↑(deriv g x)) → 0 :=
      InfinitesimalSub.of.XEq.NotInfinite hnotInf hxeq
    have hst : stdPart (↑c : ℝ*) = deriv g x :=
      EqSt.of.InfinitesimalSub (by simpa using hinf)
    simpa [EqSt] using hst.symm
  have h_gsin : ∂[x] (∂[x] u t x).arctan.sin = deriv g x := by
    change deriv (fun y => Real.sin (Real.arctan (deriv (fun y => u t y) y))) x =
      deriv g x
    have hfun :
      (fun y => Real.sin (Real.arctan (deriv (fun y => u t y) y))) = g := by
      funext y; rfl
    simp [hfun]
  rw [h_gsin, hder_eq]
  simp only [c]
  field_simp [hT]


-- created on 2026-11-05
