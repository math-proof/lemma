import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.DresdenDuSimplifiedBinet
open MetaMathlibExt


/--
[dresden_du_simplified_binet_of_initial_window](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/DresdenDuSimplifiedBinet.lean)
-/
@[path]
private lemma dresden_du_simplified_binet_of_initial_window_eq
  :
-- imply
  ∀ (k : ℕ) (_hk : 2 ≤ k) (F : ℤ → ℤ)
    (_hFzero : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n < 1 → F n = 0)
    (_hFone : F 1 = 1)
    (_hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ))) (α : ℝ)
    (_hαpos : 0 < α) (_hαroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i),
    ∀ n : ℤ, 2 - (k : ℤ) ≤ n →
    F n = ⌊((α - 1) / (2 + ((k : ℝ) + 1) * (α - 2))) * α ^ (n - 1) + 1 / 2⌋ := by
-- proof
  apply MetaMathlibExt.dresden_du_simplified_binet_of_initial_window

/--
[dresden_du_simplified_binet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/DresdenDuSimplifiedBinet.lean)
-/
@[path]
private lemma dresden_du_simplified_binet_eq
  :
-- imply
  ∀ (k : ℕ) (_hk : 2 ≤ k) (F : ℤ → ℤ) (_hFneg : ∀ n : ℤ, n < 1 → F n = 0)
    (_hFone : F 1 = 1)
    (_hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ))) (α : ℝ)
    (_hαpos : 0 < α) (_hαroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i)
    (_hαuniq : ∀ β : ℝ, 0 < β → β ^ k = ∑ i ∈ Finset.range k, β ^ i → β = α),
    ∀ n : ℤ, 2 - (k : ℤ) ≤ n →
    F n = ⌊((α - 1) / (2 + ((k : ℝ) + 1) * (α - 2))) * α ^ (n - 1) + 1 / 2⌋ := by
-- proof
  apply MetaMathlibExt.dresden_du_simplified_binet


-- created on 2026-10-20
