/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Asymptotics/CatalanOddTermsShift.lean -/


import Def.Analysis.Asymptotics.CatalanOddTermsShift
import Lemma.Real.Asymptotics.CatalanOddTermsShift


namespace MathlibExtTest.Analysis.Asymptotics.CatalanOddTermsShift

open scoped BigOperators

-- An even all-orders expansion at shift zero would contradict the uniqueness theorem.
example (a : ℕ → ℝ)
    (hexp : ∀ N : ℕ,
      Filter.Tendsto
        (fun n : ℕ => ((n : ℝ) + 0) ^ N *
          (((Nat.choose (2 * n) n : ℝ) / ((n : ℝ) + 1) *
              Real.sqrt Real.pi * Real.rpow ((n : ℝ) + 0) ((3 : ℝ) / 2) /
              (4 : ℝ) ^ n) -
            ∑ k ∈ Finset.range (N + 1), a k / ((n : ℝ) + 0) ^ k))
        Filter.atTop (nhds 0))
    (hodd : ∀ k : ℕ, a (2 * k + 1) = 0) : False := by
  have h := (MetaMathlibExt.catalan_odd_terms_shift_unique 0).mp ⟨a, hexp, hodd⟩
  norm_num at h

end MathlibExtTest.Analysis.Asymptotics.CatalanOddTermsShift
