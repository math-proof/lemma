/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/SelbergSieve.lean -/


import Def.NumberTheory.SelbergSieve
import Lemma.Nat.SelbergSieve
import Mathlib.Tactic.NormNum
open MathlibExt.SelbergSieve


namespace MathlibExtTest.NumberTheory.SelbergSieve

example (s : BoundingSieve) : 1 ∈ levelSet s 1 := by
  simp only [levelSet, Finset.mem_filter, Nat.mem_divisors]
  exact ⟨⟨one_dvd _, BoundingSieve.prodPrimes_ne_zero⟩, le_rfl⟩

example (s : BoundingSieve) (R : ℕ) (hR : 1 ≤ R) :
    0 < levelWeights s R 1 := by
  rw [levelWeights_one s R hR]
  norm_num

example (s : BoundingSieve) (R d : ℕ) (hRd : R < d) :
    levelWeights s R d = 0 := by
  by_contra hd
  exact (not_le_of_gt hRd) (levelWeights_support s R d hd)

example (s : BoundingSieve) (R d : ℕ) (hR : 1 ≤ R) (hd : d ∣ s.prodPrimes) :
    levelWeights s R d ∈ Set.Icc (-1 : ℝ) 1 := by
  simpa only [Set.mem_Icc] using (abs_le.mp (levelWeights_abs_le s R d hR hd))

example (s : BoundingSieve)
    (hnu : ∀ d : ℕ, d ∣ s.prodPrimes → 1 ≤ (d : ℝ) * s.nu d)
    (hrem : ∀ d : ℕ, d ∣ s.prodPrimes → |s.rem d| ≤ (d : ℝ)) :
    s.errSum (BoundingSieve.lambdaSquared (levelWeights s 2)) ≤ 4096 := by
  have h := levelWeights_errSum_le s 2 (by norm_num) hnu hrem
  norm_num at h
  exact h

end MathlibExtTest.NumberTheory.SelbergSieve
