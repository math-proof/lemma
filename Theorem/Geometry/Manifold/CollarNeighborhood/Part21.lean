/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part20
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarFiberDenomTwoPos (p : Set.Icc (0 : ℝ) 1) :
    0 < 2 - p.val := by
  linarith [p.property.2]

theorem collarFiberDenomHalfPos (p : Set.Icc (0 : ℝ) 1) :
    0 < p.val + 1 / 2 := by
  linarith [p.property.1]

theorem collarFiberMap_lower {p q s : ℝ} (h : s ≤ -p) :
    collarFiberMap p q s = -2 + (s + 2) * (2 - q) / (2 - p) := by
  simp [collarFiberMap, h]

theorem collarFiberMap_middle {p q s : ℝ} (h₁ : ¬ s ≤ -p)
    (h₂ : s ≤ (1 / 2 : ℝ)) :
    collarFiberMap p q s = -q + (s + p) * (q + 1 / 2) / (p + 1 / 2) := by
  rw [collarFiberMap, ite_eq_right h₁, ite_eq_left h₂]

theorem collarFiberMap_upper (p : Set.Icc (0 : ℝ) 1) {q s : ℝ}
    (h : ¬ s ≤ (1 / 2 : ℝ)) : collarFiberMap p q s = s := by
  have h' : ¬ s ≤ -p.val := by linarith [p.property.1]
  rw [collarFiberMap, ite_eq_right h', ite_eq_right h]

theorem collarFiberMap_lower_bounds (p q : Set.Icc (0 : ℝ) 1) {s : ℝ}
    (hs : -2 ≤ s) (hsp : s ≤ -p.val) :
    -2 ≤ collarFiberMap p.val q.val s ∧ collarFiberMap p.val q.val s ≤ -q.val := by
  rw [collarFiberMap_lower hsp]
  have hp : 0 < 2 - p.val := collarFiberDenomTwoPos p
  have hq : 0 ≤ 2 - q.val := by linarith [q.property.2]
  have hs0 : 0 ≤ s + 2 := by linarith
  have hs1 : s + 2 ≤ 2 - p.val := by linarith
  constructor
  · have : 0 ≤ (s + 2) * (2 - q.val) / (2 - p.val) :=
      div_nonneg (mul_nonneg hs0 hq) hp.le
    linarith
  · have hmul := mul_le_mul_of_nonneg_right hs1 hq
    have hdiv : (s + 2) * (2 - q.val) / (2 - p.val) ≤ 2 - q.val := by
      apply (div_le_iff₀ hp).2
      simpa [mul_comm] using hmul
    linarith

theorem collarFiberMap_middle_bounds (p q : Set.Icc (0 : ℝ) 1) {s : ℝ}
    (hsp : -p.val < s) (hs : s ≤ (1 / 2 : ℝ)) :
    -q.val < collarFiberMap p.val q.val s ∧
      collarFiberMap p.val q.val s ≤ (1 / 2 : ℝ) := by
  rw [collarFiberMap_middle (not_le_of_gt hsp) hs]
  have hp : 0 < p.val + 1 / 2 := collarFiberDenomHalfPos p
  have hq : 0 < q.val + 1 / 2 := by linarith [q.property.1]
  have hs0 : 0 < s + p.val := by linarith
  have hs1 : s + p.val ≤ p.val + 1 / 2 := by linarith
  constructor
  · have : 0 < (s + p.val) * (q.val + 1 / 2) / (p.val + 1 / 2) :=
      div_pos (mul_pos hs0 hq) hp
    linarith
  · have hmul := mul_le_mul_of_nonneg_right hs1 hq.le
    have hdiv :
        (s + p.val) * (q.val + 1 / 2) / (p.val + 1 / 2) ≤ q.val + 1 / 2 := by
      apply (div_le_iff₀ hp).2
      simpa [mul_comm] using hmul
    linarith

theorem collarFiberMap_mem_Ico (p q : Set.Icc (0 : ℝ) 1)
    (s : Set.Ico (-2 : ℝ) 1) :
    collarFiberMap p.val q.val s.val ∈ Set.Ico (-2 : ℝ) 1 := by
  by_cases hsp : s.val ≤ -p.val
  · have h := collarFiberMap_lower_bounds p q s.property.1 hsp
    exact ⟨h.1, lt_of_le_of_lt h.2 (by linarith [q.property.1])⟩
  · by_cases hs : s.val ≤ (1 / 2 : ℝ)
    · have h := collarFiberMap_middle_bounds p q (lt_of_not_ge hsp) hs
      exact ⟨by linarith [q.property.2, h.1], lt_of_le_of_lt h.2 (by norm_num)⟩
    · rw [collarFiberMap_upper p hs]
      exact s.property

theorem collarFiberMap_inverse_lower (p q : Set.Icc (0 : ℝ) 1) {s : ℝ}
    (hs : -2 ≤ s) (hsp : s ≤ -p.val) :
    collarFiberMap q.val p.val (collarFiberMap p.val q.val s) = s := by
  have hb := (collarFiberMap_lower_bounds p q hs hsp).2
  rw [collarFiberMap_lower hb, collarFiberMap_lower hsp]
  field_simp [ne_of_gt (collarFiberDenomTwoPos p),
    ne_of_gt (collarFiberDenomTwoPos q)]
  ring

theorem collarFiberMap_inverse_middle (p q : Set.Icc (0 : ℝ) 1) {s : ℝ}
    (hsp : -p.val < s) (hs : s ≤ (1 / 2 : ℝ)) :
    collarFiberMap q.val p.val (collarFiberMap p.val q.val s) = s := by
  have hb := collarFiberMap_middle_bounds p q hsp hs
  rw [collarFiberMap_middle (not_le_of_gt hb.1) hb.2,
    collarFiberMap_middle (not_le_of_gt hsp) hs]
  have hp : p.val + 1 / 2 ≠ 0 := ne_of_gt (collarFiberDenomHalfPos p)
  have hq : q.val + 1 / 2 ≠ 0 := ne_of_gt (collarFiberDenomHalfPos q)
  have hc :
      -q.val + (s + p.val) * (q.val + 1 / 2) / (p.val + 1 / 2) + q.val =
        (s + p.val) * (q.val + 1 / 2) / (p.val + 1 / 2) := by ring
  rw [hc, div_mul_cancel₀ _ hp, mul_div_cancel_right₀ _ hq]
  ring

theorem collarFiberMap_inverse_upper (p q : Set.Icc (0 : ℝ) 1) {s : ℝ}
    (hs : (1 / 2 : ℝ) < s) :
    collarFiberMap q.val p.val (collarFiberMap p.val q.val s) = s := by
  rw [collarFiberMap_upper p (not_le_of_gt hs),
    collarFiberMap_upper q (not_le_of_gt hs)]

theorem collarFiberMap_inverse (p q : Set.Icc (0 : ℝ) 1)
    (s : Set.Ico (-2 : ℝ) 1) :
    collarFiberMap q.val p.val (collarFiberMap p.val q.val s.val) = s.val := by
  by_cases hsp : s.val ≤ -p.val
  · exact collarFiberMap_inverse_lower p q s.property.1 hsp
  · by_cases hs : s.val ≤ (1 / 2 : ℝ)
    · exact collarFiberMap_inverse_middle p q (lt_of_not_ge hsp) hs
    · exact collarFiberMap_inverse_upper p q (lt_of_not_ge hs)

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
