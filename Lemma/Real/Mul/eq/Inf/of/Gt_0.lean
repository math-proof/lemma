import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Algebra.Order.Field
import sympy.Basic


@[path]
private lemma main
  {a : ℝ}
  {f : α → ℝ}
  {S : Set α}
-- given
  (h₀ : 0 < a)
  (h₁ : S.Nonempty)
  (h₂ : BddBelow (f '' S)) :
-- imply
  a * sInf (f '' S) = sInf ((fun x => a * f x) '' S) := by
-- proof
  have hmono : Monotone (fun y : ℝ => a * y) := monotone_mul_left_of_nonneg h₀.le
  have hcont : ContinuousAt (fun y : ℝ => a * y) (sInf (f '' S)) :=
    (continuous_const_mul a).continuousAt
  rw [hmono.map_csInf_of_continuousAt hcont (h₁.image f) h₂]
  rw [← Set.image_comp]
  rfl


-- created on 2026-10-11
-- updated on 2026-10-17
