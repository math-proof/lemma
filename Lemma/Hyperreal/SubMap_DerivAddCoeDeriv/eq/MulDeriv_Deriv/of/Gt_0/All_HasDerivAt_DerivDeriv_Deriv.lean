import Lemma.Hyperreal.SubMapAddCoe.eq.MulDeriv.of.All_HasDerivAt_Deriv
import Initialize.Tactic.Attr.Basic
open Filter Hyperreal


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x : ℝ}
  {Δx : ℝ*}
-- given
  (hf : ∀ y, HasDerivAt (deriv f) (deriv (deriv f) x) y)
  (_ : Δx > 0) :
-- imply
  (show ℝ* from Germ.map (deriv f) ((x : ℝ*) + Δx)) - ↑(deriv f x) =
    ↑(deriv (deriv f) x) * Δx := by
-- proof
  apply SubMapAddCoe.eq.MulDeriv.of.All_HasDerivAt_Deriv (g := deriv f)
  exact hf


-- created on 2026-11-04
