import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic
import sympy.Basic


@[path]
private lemma main
  [Fintype Ω]
-- given
  (X : Ω → ℝ)
  (t : ℝ) :
-- imply
  ∃ q, t < q ∧ {ω | X ω ≤ t} = {ω | X ω < q} := by
-- proof
  classical
  let S := (Finset.univ.image X).filter (t < ·)
  if h : S.Nonempty then
    obtain ⟨-, hq⟩ := Finset.mem_filter.mp (S.min'_mem h)
    refine ⟨S.min' h, hq, Set.ext fun ω => ⟨fun hω => lt_of_le_of_lt hω hq, fun hω => ?_⟩⟩
    by_contra hc
    exact (S.min'_le (X ω) (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem X (Finset.mem_univ ω), not_le.mp hc⟩)).not_gt hω
  else
    refine ⟨t + 1, by linarith, Set.ext fun ω => ?_⟩
    have := not_lt.mp fun hc => h ⟨X ω, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem X (Finset.mem_univ ω), hc⟩⟩
    simp only [Set.mem_ofPred_eq]
    constructor <;>
      intro <;>
      linarith


-- created on 2026-09-26
-- updated on 2026-10-12
