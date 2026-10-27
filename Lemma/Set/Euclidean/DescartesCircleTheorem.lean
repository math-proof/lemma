import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped BigOperators


namespace MetaMathlibExt

/--
[descartes_sq_dist](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/DescartesCircleTheorem.lean)
-/
@[path]
private lemma descartes_sq_dist (p q : EuclideanSpace ℝ (Fin 2)) :
  dist p q ^ 2 = (p.ofLp 0 - q.ofLp 0) ^ 2 + (p.ofLp 1 - q.ofLp 1) ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[descartes_planar_relation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/DescartesCircleTheorem.lean)
-/
@[path]
private lemma descartes_planar_relation (c : Fin 4 → EuclideanSpace ℝ (Fin 2)) :
  4 * dist (c 0) (c 1) ^ 2 * dist (c 0) (c 2) ^ 2 * dist (c 0) (c 3) ^ 2 +
    (dist (c 0) (c 1) ^ 2 + dist (c 0) (c 2) ^ 2 - dist (c 1) (c 2) ^ 2) *
      (dist (c 0) (c 1) ^ 2 + dist (c 0) (c 3) ^ 2 - dist (c 1) (c 3) ^ 2) *
      (dist (c 0) (c 2) ^ 2 + dist (c 0) (c 3) ^ 2 - dist (c 2) (c 3) ^ 2) -
    dist (c 0) (c 1) ^ 2 *
      (dist (c 0) (c 2) ^ 2 + dist (c 0) (c 3) ^ 2 - dist (c 2) (c 3) ^ 2) ^ 2 -
    dist (c 0) (c 2) ^ 2 *
      (dist (c 0) (c 1) ^ 2 + dist (c 0) (c 3) ^ 2 - dist (c 1) (c 3) ^ 2) ^ 2 -
    dist (c 0) (c 3) ^ 2 *
      (dist (c 0) (c 1) ^ 2 + dist (c 0) (c 2) ^ 2 - dist (c 1) (c 2) ^ 2) ^ 2 = 0 := by
  rw [descartes_sq_dist (c 0) (c 1), descartes_sq_dist (c 0) (c 2),
    descartes_sq_dist (c 0) (c 3), descartes_sq_dist (c 1) (c 2),
    descartes_sq_dist (c 1) (c 3), descartes_sq_dist (c 2) (c 3)]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[descartes_signed_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/DescartesCircleTheorem.lean)
-/
@[path]
private lemma descartes_signed_algebra (s : Fin 4 → ℝ) (hs : ∀ i, s i ≠ 0)
  (hpoly :
    4 * (s 0 + s 1) ^ 2 * (s 0 + s 2) ^ 2 * (s 0 + s 3) ^ 2 +
      ((s 0 + s 1) ^ 2 + (s 0 + s 2) ^ 2 - (s 1 + s 2) ^ 2) *
        ((s 0 + s 1) ^ 2 + (s 0 + s 3) ^ 2 - (s 1 + s 3) ^ 2) *
        ((s 0 + s 2) ^ 2 + (s 0 + s 3) ^ 2 - (s 2 + s 3) ^ 2) -
      (s 0 + s 1) ^ 2 *
        ((s 0 + s 2) ^ 2 + (s 0 + s 3) ^ 2 - (s 2 + s 3) ^ 2) ^ 2 -
      (s 0 + s 2) ^ 2 *
        ((s 0 + s 1) ^ 2 + (s 0 + s 3) ^ 2 - (s 1 + s 3) ^ 2) ^ 2 -
      (s 0 + s 3) ^ 2 *
        ((s 0 + s 1) ^ 2 + (s 0 + s 2) ^ 2 - (s 1 + s 2) ^ 2) ^ 2 = 0) :
  (∑ i : Fin 4, 1 / s i) ^ 2 = 2 * ∑ i : Fin 4, (1 / s i) ^ 2 := by
  simp only [Fin.sum_univ_four]
  field_simp [hs 0, hs 1, hs 2, hs 3]
  ring_nf at hpoly ⊢
  nlinarith [hpoly]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[descartes_of_signed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/DescartesCircleTheorem.lean)
-/
@[path]
private lemma descartes_of_signed (c : Fin 4 → EuclideanSpace ℝ (Fin 2))
  (s k : Fin 4 → ℝ) (hs : ∀ i, s i ≠ 0) (hk : ∀ i, k i = 1 / s i)
  (hdist : ∀ i j, i ≠ j → dist (c i) (c j) ^ 2 = (s i + s j) ^ 2) :
  (∑ i : Fin 4, k i) ^ 2 = 2 * ∑ i : Fin 4, k i ^ 2 := by
  have hplanar := descartes_planar_relation c
  rw [hdist 0 1 (by decide), hdist 0 2 (by decide), hdist 0 3 (by decide),
    hdist 1 2 (by decide), hdist 1 3 (by decide), hdist 2 3 (by decide)] at hplanar
  simpa only [hk] using descartes_signed_algebra s hs hplanar

end MetaMathlibExt

namespace MetaMathlibExt

/--
[descartes_circle_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/DescartesCircleTheorem.lean)
-/
@[path]
lemma descartes_circle_theorem
  {c : Fin 4 → EuclideanSpace ℝ (Fin 2)}
  {r k : Fin 4 → ℝ} :
-- imply
  (∀ i, 0 < r i) →
    (((∀ i j, i ≠ j → dist (c i) (c j) = r i + r j) ∧ ∀ i, k i = 1 / r i) ∨
    ∃ e : Fin 4, k e = -1 / r e ∧ (∀ j, j ≠ e → k j = 1 / r j) ∧
    (∀ j, j ≠ e → dist (c e) (c j) = r e - r j) ∧
    ∀ i j, i ≠ e → j ≠ e → i ≠ j → dist (c i) (c j) = r i + r j) →
    (∑ i : Fin 4, k i) ^ 2 = 2 * ∑ i : Fin 4, k i ^ 2 := by
-- proof
  intro hr htan
  obtain ⟨hdist, hk⟩ | ⟨e, hke, hk, hdist_e, hdist⟩ := htan
  · apply descartes_of_signed c r k
    · exact fun i ↦ ne_of_gt (hr i)
    · exact hk
    · intro i j hij
      rw [hdist i j hij]
  · let s : Fin 4 → ℝ := fun i ↦ if i = e then -r i else r i
    apply descartes_of_signed c s k
    · intro i
      dsimp [s]
      split_ifs
      · exact neg_ne_zero.mpr (ne_of_gt (hr i))
      · exact ne_of_gt (hr i)
    · intro i
      by_cases hi : i = e
      · subst i
        have hse : s e = -r e := by simp [s]
        rw [hse, hke]
        field_simp [ne_of_gt (hr e)]
      · have hsi : s i = r i := by simp [s, hi]
        rw [hsi]
        exact hk i hi
    · intro i j hij
      by_cases hi : i = e
      · subst i
        have hj : j ≠ e := Ne.symm hij
        have hse : s e = -r e := by simp [s]
        have hsj : s j = r j := by simp [s, hj]
        rw [hse, hsj, hdist_e j hj]
        ring
      · by_cases hj : j = e
        · subst j
          have hsi : s i = r i := by simp [s, hi]
          have hse : s e = -r e := by simp [s]
          rw [hsi, hse, dist_comm, hdist_e i hi]
          ring
        · have hsi : s i = r i := by simp [s, hi]
          have hsj : s j = r j := by simp [s, hj]
          rw [hsi, hsj, hdist i j hi hj hij]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
