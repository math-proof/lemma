import Lemma.Hyperreal.SubMap_DerivAddCoeDeriv.eq.MulDeriv_Deriv.of.Gt_0.All_HasDerivAt_DerivDeriv_Deriv
import Instance.Analysis.Hyperreal.Coe
import Initialize.Tactic.Attr.Basic
import Syntax.Analysis.Real.Limits
import Theorem.Analysis.Real.Relational
open Real Hyperreal Filter


/--
Infinitesimal increment (NSA microaffinity) of `deriv`, as a Hyperreal `≈`.

For a positive infinitesimal `Δx : ℝ*` with `Δx → 0⁺`, and when
`deriv f` has constant derivative `deriv (deriv f) x` everywhere
(`∀ y, HasDerivAt (deriv f) (deriv (deriv f) x) y`),
\[
  \frac{*(deriv\,f)(x+Δx)-\uparrow(deriv\,f\,x)}{Δx}
    \approx \uparrow\bigl(deriv(deriv\,f)\,x\bigr).
\]
In Lean the nonstandard extension of `deriv f` is written
`@id (ℝ* → ℝ*) (deriv f : ℝ → ℝ) (↑x + Δx)`, using
`Instance.Analysis.Hyperreal.Coe` (`Coe (ℝ → ℝ) (ℝ* → ℝ*)` via `Germ.map`).
Bare `(deriv f : ℝ* → ℝ*)` still does not elaborate (expected type infects `deriv`).

Proved from the undivided Hyperreal equality
`Hyperreal.SubMap_DerivAddCoeDeriv.eq.MulDeriv_Deriv.of.Gt_0.All_HasDerivAt_DerivDeriv_Deriv`
by dividing by `Δx > 0` (from `Δx → 0⁺`).
-/
@[path]
private lemma main
  {f : ℝ → ℝ}
  {x : ℝ}
  {Δx : ℝ*}
-- given
  (hf : ∀ y, HasDerivAt (deriv f) (deriv (deriv f) x) y)
  (h_Δx : Δx → 0⁺) :
-- imply
  (@id (ℝ* → ℝ*) (deriv f : ℝ → ℝ) ((x : ℝ*) + Δx) -
      ↑(deriv f x)) / Δx ≈
    ↑(deriv (deriv f) x) := by
-- proof
  have heq :
    (show ℝ* from Germ.map (deriv f) ((x : ℝ*) + Δx)) - ↑(deriv f x) =
      ↑(deriv (deriv f) x) * Δx :=
    SubMap_DerivAddCoeDeriv.eq.MulDeriv_Deriv.of.Gt_0.All_HasDerivAt_DerivDeriv_Deriv
      (f := f) (x := x) (Δx := Δx) hf h_Δx.1
  have hdiv :
    (@id (ℝ* → ℝ*) (deriv f : ℝ → ℝ) ((x : ℝ*) + Δx) - ↑(deriv f x)) / Δx =
      ↑(deriv (deriv f) x) := by
    -- `@id (ℝ* → ℝ*)` is the Coe `Germ.map`
    change ((show ℝ* from Germ.map (deriv f) ((x : ℝ*) + Δx)) - ↑(deriv f x)) / Δx =
      ↑(deriv (deriv f) x)
    rw [heq, mul_div_cancel_right₀ _ h_Δx.1.ne']
  rw [hdiv]


-- created on 2026-11-05
