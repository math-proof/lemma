/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Recurrences/DresdenDuSimplifiedBinet.lean -/


import Mathlib.Tactic
import sympy.atlas.NumberTheory.Recurrences.DresdenDuSimplifiedBinet
import Lemma.Nat.Recurrences.DresdenDuSimplifiedBinet

namespace MetaMathlibExt

-- For `k = 2`, values below zero are unrestricted because the conclusion starts at zero.
example (F : ℤ → ℤ) (hFzero : ∀ n : ℤ, 0 ≤ n → n < 1 → F n = 0) (hFone : F 1 = 1)
    (hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range 2, F (n - 1 - (i : ℤ)))
    (α : ℝ) (hαpos : 0 < α) (hαroot : α ^ 2 = ∑ i ∈ Finset.range 2, α ^ i) :
    ∀ n : ℤ, 0 ≤ n →
      F n = ⌊((α - 1) / (2 + ((2 : ℝ) + 1) * (α - 2))) * α ^ (n - 1) + 1 / 2⌋ := by
  simpa using dresden_du_simplified_binet_of_initial_window 2 (by norm_num) F hFzero hFone
    hFrec α hαpos hαroot

end MetaMathlibExt
