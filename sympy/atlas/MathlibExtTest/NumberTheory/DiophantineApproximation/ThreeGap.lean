/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DiophantineApproximation/ThreeGap.lean -/


import sympy.atlas.NumberTheory.DiophantineApproximation.ThreeGap
import Lemma.Nat.DiophantineApproximation.ThreeGap

namespace MetaMathlibExt

example (α d : ℝ) : IsThreeGapLength 1 α d ↔ d = 1 := by
  have hpoint (x : ℝ) : IsThreeGapPoint 1 α x ↔ x = 0 := by
    constructor
    · rintro ⟨k, hk, rfl⟩
      interval_cases k
      simp [Int.fract]
    · rintro rfl
      exact ⟨0, by omega, by simp [Int.fract]⟩
  simp [IsThreeGapLength, hpoint]

example (d : ℝ) :
    IsThreeGapLength 2 (Real.sqrt 2) d ↔
      d = Real.sqrt 2 - 1 ∨ d = 2 - Real.sqrt 2 := by
  have hpoint (x : ℝ) :
      IsThreeGapPoint 2 (Real.sqrt 2) x ↔ x = 0 ∨ x = Real.sqrt 2 - 1 := by
    have hfloor : ⌊Real.sqrt 2⌋ = (1 : ℤ) := by
      rw [Int.floor_eq_iff]
      norm_num
    constructor
    · rintro ⟨k, hk, rfl⟩
      interval_cases k <;> simp [Int.fract, hfloor]
    · rintro (rfl | rfl)
      · exact ⟨0, by omega, by simp [Int.fract]⟩
      · exact ⟨1, by omega, by simp [Int.fract, hfloor]⟩
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt_nonneg := Real.sqrt_nonneg 2
  have hone : 1 < Real.sqrt 2 := by nlinarith
  have hnot : ¬ Real.sqrt 2 < 1 := not_lt_of_ge hone.le
  have hwrap : 1 - (Real.sqrt 2 - 1) = 2 - Real.sqrt 2 := by ring
  simp [IsThreeGapLength, hpoint, hone, hnot, hwrap]

example :
    ∃ G : Finset ℝ,
      (∀ d : ℝ, d ∈ G ↔ IsThreeGapLength 2 (Real.sqrt 2) d) ∧ G.card = 2 := by
  classical
  have hpoint (x : ℝ) :
      IsThreeGapPoint 2 (Real.sqrt 2) x ↔ x = 0 ∨ x = Real.sqrt 2 - 1 := by
    have hfloor : ⌊Real.sqrt 2⌋ = (1 : ℤ) := by
      rw [Int.floor_eq_iff]
      norm_num
    constructor
    · rintro ⟨k, hk, rfl⟩
      interval_cases k <;> simp [Int.fract, hfloor]
    · rintro (rfl | rfl)
      · exact ⟨0, by omega, by simp [Int.fract]⟩
      · exact ⟨1, by omega, by simp [Int.fract, hfloor]⟩
  have hlength (d : ℝ) :
      IsThreeGapLength 2 (Real.sqrt 2) d ↔
        d = Real.sqrt 2 - 1 ∨ d = 2 - Real.sqrt 2 := by
    have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hsqrt_nonneg := Real.sqrt_nonneg 2
    have hone : 1 < Real.sqrt 2 := by nlinarith
    have hnot : ¬ Real.sqrt 2 < 1 := not_lt_of_ge hone.le
    have hwrap : 1 - (Real.sqrt 2 - 1) = 2 - Real.sqrt 2 := by ring
    simp [IsThreeGapLength, hpoint, hone, hnot, hwrap]
  obtain ⟨G, hG, _, _⟩ :=
    three_gap 2 (by norm_num) (Real.sqrt 2) irrational_sqrt_two
  refine ⟨G, hG, ?_⟩
  have hG_eq : G = {Real.sqrt 2 - 1, 2 - Real.sqrt 2} := by
    ext d
    rw [hG d, hlength]
    simp
  have hne : Real.sqrt 2 - 1 ≠ 2 - Real.sqrt 2 := by
    intro h
    have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  rw [hG_eq]
  simp [hne]

end MetaMathlibExt
