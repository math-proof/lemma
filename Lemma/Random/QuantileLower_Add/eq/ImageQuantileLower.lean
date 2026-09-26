import sympy.stats.quantile
import sympy.Basic
import Lemma.Random.IsQuantileLower
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω}
-- given
  (X : Ω → ℝ)
  (α c : ℝ) :
-- imply
  quantileLower μ (fun ω => X ω + c) α = (fun x => x + c) '' quantileLower μ X α := by
-- proof
  ext v
  constructor
  · intro h
    refine ⟨v - c, (Random.IsQuantileLower X α (v - c) c).mpr ?_, sub_add_cancel v c⟩
    rwa [sub_add_cancel]
  · rintro ⟨q, hq, rfl⟩
    exact (Random.IsQuantileLower X α q c).mp hq


-- created on 2026-09-26
