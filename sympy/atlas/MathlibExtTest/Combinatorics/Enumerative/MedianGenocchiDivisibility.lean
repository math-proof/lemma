/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MedianGenocchiDivisibility.lean -/


import sympy.atlas.Combinatorics.Enumerative.MedianGenocchiDivisibility
import Lemma.Finset.Enumerative.MedianGenocchiDivisibility
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.BigOperators


namespace MathlibExtTest.Combinatorics.Enumerative.MedianGenocchiDivisibility

-- The n = 3 theorem and the direct value computation force quotient seven.
example (h : 1 ≤ (3 : ℕ)) : ∃ z : ℤ,
    MetaMathlibExt.medianGenocchiOdd 4 = (8 : ℚ) * z ∧
      z = 7 ∧ Int.ModEq 6 z 1 := by
  obtain ⟨z, hvalue, hmod⟩ :=
    MetaMathlibExt.medianGenocchiOdd_divisibility 3 h
  have hzq : (z : ℚ) = 7 := by
    rw [medianGenocchiOdd_four] at hvalue
    norm_num at hvalue
    linarith
  have hz : z = 7 := by exact_mod_cast hzq
  refine ⟨z, ?_, hz, ?_⟩
  · norm_num at hvalue ⊢
    exact hvalue
  · have hodd : Odd (3 : ℕ) := by decide
    simpa only [hodd, ↓reduceIte] using hmod

-- The n = 4 theorem gives the even quotient's concrete residue divisibility.
example (h : 1 ≤ (4 : ℕ)) : ∃ z : ℤ,
    MetaMathlibExt.medianGenocchiOdd 5 = (16 : ℚ) * z ∧ 6 ∣ z - 4 := by
  obtain ⟨z, hvalue, hmod⟩ :=
    MetaMathlibExt.medianGenocchiOdd_divisibility 4 h
  refine ⟨z, ?_, (dvd_sub_comm.mp hmod.dvd)⟩
  norm_num at hvalue ⊢
  exact hvalue

end MathlibExtTest.Combinatorics.Enumerative.MedianGenocchiDivisibility
