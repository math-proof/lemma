import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.SpiveyBellNumberAddition
open scoped BigOperators
open MetaMathlibExt


/--
[spivey_bell_number_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SpiveyBellNumberAddition.lean)
-/
@[path]
private lemma spivey_bell_number_add_eq
  {m n : ℕ} :
-- imply
  (n + m).bell = ∑ j ∈ Finset.range (m + 1), ∑ k ∈
    Finset.range (n + 1), j ^ (n - k) * m.stirlingSecond j * n.choose k * k.bell := by
-- proof
  apply MetaMathlibExt.spivey_bell_number_add m n

/--
[spivey_bell_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SpiveyBellNumberAddition.lean)
-/
@[path]
private lemma spivey_bell_recurrence_eq
  {n m : ℕ} :
-- imply
  Nat.bell (n + m) =
    ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
    j ^ (n - k) * Nat.stirlingSecond m j * Nat.choose n k * Nat.bell k := by
-- proof
  apply MetaMathlibExt.spivey_bell_recurrence n m


-- created on 2026-10-20
