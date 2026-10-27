import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[roth_exists_row_det_ne_zero_of_mem_span](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {k : ℕ} [CommRing K]
  (A : Matrix (Fin k) (Fin k) K)
  (i : Fin k)
  (S : Set (Fin k → K))
-- given
  (hA : A.det ≠ 0)
  (hi : A i ∈ Submodule.span K S) :
-- imply
  ∃ v ∈ S, (A.updateRow i v).det ≠ 0 := by
-- proof
  classical
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hall : ∀ v ∈ Submodule.span K S, (A.updateRow i v).det = 0 := by
    intro v hv
    apply Submodule.span_induction (R := K) (s := S)
      (p := fun v _ ↦ (A.updateRow i v).det = 0)
    ·
      intro v hv
      apply h v hv
    ·
      apply Matrix.det_eq_zero_of_row_eq_zero i
      intro j
      simp [Matrix.updateRow_apply]
    ·
      intro u v _ _ hu hv
      rw [Matrix.det_updateRow_add, hu, hv, add_zero]
    ·
      intro c v _ hv
      rw [Matrix.det_updateRow_smul, hv, mul_zero]
    ·
      apply hv
  have := hall (A i) hi
  rw [Matrix.updateRow_eq_self] at this
  apply hA this


-- created on 2026-10-21
