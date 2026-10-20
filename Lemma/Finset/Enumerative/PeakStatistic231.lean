import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.PeakStatistic231
open MetaMathlibExt


/--
[card_permutations_avoiding_231_with_peak_count](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean)
-/
@[path]
private lemma card_permutations_avoiding_231_with_peak_count_eq
  {n k : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    (∀ i j l : Fin n, i < j → j < l → ¬ (σ l < σ i ∧ σ i < σ j)) ∧
    (Finset.univ.filter (fun i : Fin n =>
    ∃ iPrev iNext : Fin n,
    iPrev.val + 1 = i.val ∧ i.val + 1 = iNext.val ∧
    σ iPrev < σ i ∧ σ iNext < σ i)).card = k)).card =
    2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) * Nat.choose (2 * k) k /
    (k + 1) := by
-- proof
  apply MetaMathlibExt.card_permutations_avoiding_231_with_peak_count n k hn


-- created on 2026-10-20
