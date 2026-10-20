import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.SetPartitionPeaks
open scoped BigOperators
open MetaMathlibExt


/--
[total_peaks_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SetPartitionPeaks.lean)
-/
@[path]
private lemma total_peaks_canonical_eq
  {n k : ℕ} :
-- imply
  (∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin k =>
    Function.Surjective f ∧
    ∀ i : Fin n, ∀ m : Fin k,
    m.val < (f i).val → ∃ j : Fin n, j.val < i.val ∧ f j = m),
    (Finset.univ.filter (fun i : Fin n =>
    i.val ≠ 0 ∧
    if h : i.val + 1 < n then
    (f ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩).val <
    (f i).val ∧
    (f ⟨i.val + 1, h⟩).val < (f i).val
    else False)).card) =
    Nat.choose k 2 * Nat.stirlingSecond (n - 1) k +
    ∑ j ∈ Finset.Icc 2 k,
    (j * Nat.choose j 2 - Nat.choose (j + 1) 3) *
    ∑ i ∈ Finset.Icc 3 (n - k),
    j ^ (i - 3) * Nat.stirlingSecond (n - i) k := by
-- proof
  apply MetaMathlibExt.total_peaks_canonical n k


-- created on 2026-10-20
