import sympy.stats.value_at_risk
import sympy.Basic
import Lemma.Random.QuantileLower_Add.eq.ImageQuantileLower
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω}
  {X : Ω → ℝ}
  {α v : ℝ}
-- given
  (h₀ : IsVaR μ X α v)
  (c : ℝ) :
-- imply
  IsVaR μ (fun ω => X ω + c) α (v + c) := by
-- proof
  constructor
  rw [Random.QuantileLower_Add.eq.ImageQuantileLower]
  exact (Monotone.monotoneOn (f := fun x => x + c) (fun _ _ h => (add_le_add_iff_right c).mpr h) _).map_isGreatest h₀.isGreatest


-- created on 2026-09-26
