/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/Interlacing.lean -/

import Def.Algebra.Polynomial.Interlacing
import Lemma.Polynomial.Interlacing
import Def.MathlibExtTest.Algebra.Polynomial.Interlacing
open scoped BigOperators ComplexOrder


namespace MathlibExtTest.Algebra.Polynomial.Interlacing

noncomputable section

-- Between an upper interlacing point and the largest root, its value is nonpositive.
example : ((linearPolynomial 2).eval ((3 / 2 : ℝ) : ℂ)).re ≤ 0 := by
  apply Polynomial.eval_re_nonpos_of_upperInterlacing
      (linearPolynomial_monic 2) (linearPolynomial_realRooted 2)
      (a := 0) (x := 3 / 2)
  · simpa [family] using family_upperInterlacing 1
  · norm_num
  · rw [linearPolynomial_maxRealRoot]
    norm_num
  · rw [linearPolynomial_natDegree]
    norm_num

-- A two-polynomial family with a common interlacing point selects a bounded member.
example :
    ∃ i, (family i).maxRealRoot ≤
      (∑ j, (weights j : ℂ) • family j).maxRealRoot := by
  apply Polynomial.exists_maxRealRoot_le_weightedSum_of_commonUpperInterlacing
  · intro i
    fin_cases i <;> norm_num [weights]
  · intro i
    fin_cases i <;> exact linearPolynomial_monic _
  · intro i
    fin_cases i <;> exact linearPolynomial_realRooted _
  · intro i
    fin_cases i <;> simp [family, linearPolynomial_natDegree]
  · exact ⟨0, family_upperInterlacing⟩
  · rw [weightedSum_eq]
    exact linearPolynomial_monic _
  · rw [weightedSum_eq]
    exact linearPolynomial_realRooted _

-- Real-rootedness of every segment also selects a bounded family member.
example :
    ∃ i, (family i).maxRealRoot ≤
      (∑ j, (weights j : ℂ) • family j).maxRealRoot := by
  apply Polynomial.exists_maxRealRoot_le_weightedSum_of_segment_realRooted
      (hne := inferInstance) (n := 1)
  · norm_num
  · intro i
    fin_cases i <;> norm_num [weights]
  · intro i
    fin_cases i <;>
      exact ⟨linearPolynomial_natDegree _, linearPolynomial_monic _⟩
  · rw [weightedSum_eq]
    exact ⟨linearPolynomial_natDegree _, linearPolynomial_monic _⟩
  · intro i t ht
    rw [weightedSum_eq]
    fin_cases i
    · change ((1 - (t : ℂ)) • linearPolynomial (3 / 2) +
          (t : ℂ) • linearPolynomial 1).IsRealRooted
      rw [linearCombination_eq]
      exact linearPolynomial_realRooted _
    · change ((1 - (t : ℂ)) • linearPolynomial (3 / 2) +
          (t : ℂ) • linearPolynomial 2).IsRealRooted
      rw [linearCombination_eq]
      exact linearPolynomial_realRooted _

end
end MathlibExtTest.Algebra.Polynomial.Interlacing
