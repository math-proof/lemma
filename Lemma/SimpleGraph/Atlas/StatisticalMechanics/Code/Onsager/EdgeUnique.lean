import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.EdgeUnique
open StatMech StatMech.Onsager StatMech.Onsager.EdgeUnique


/--
[not_add_two_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/EdgeUnique.lean)
-/
@[path]
private lemma not_add_two_self_eq
  {n : ℕ}
  [NeZero n]
  {k : Fin n}
-- given
  (hn : 3 ≤ n) :
-- imply
  k + 1 + 1 ≠ k := by
-- proof
  apply StatMech.Onsager.EdgeUnique.not_add_two_self hn k

/--
[midSet_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/EdgeUnique.lean)
-/
@[path]
private lemma midSet_endpoints_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hk : k ∈ midSet d a b) :
-- imply
  (pos d k = (a, b) ∧ pos d (k + 1) = (a + 1, b)) ∨ (pos d k = (a + 1, b) ∧ pos d (k + 1) = (a, b)) := by
-- proof
  apply StatMech.Onsager.EdgeUnique.midSet_endpoints d hclosed a b k hk

/--
[straddleSet_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/EdgeUnique.lean)
-/
@[path]
private lemma straddleSet_endpoints_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hk : k ∈ straddleSet d a b) :
-- imply
  (pos d k = (a + 1, b) ∧ pos d (k + 1) = (a + 1, b + 1)) ∨ (pos d k = (a + 1, b + 1) ∧ pos d (k + 1) = (a + 1, b)) := by
-- proof
  apply StatMech.Onsager.EdgeUnique.straddleSet_endpoints d hclosed a b k hk

/--
[midSet_card_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/EdgeUnique.lean)
-/
@[path]
private lemma midSet_card_le_one_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n) :
-- imply
  (midSet d a b).card ≤ 1 := by
-- proof
  apply StatMech.Onsager.EdgeUnique.midSet_card_le_one d hclosed hsimple hn a b

/--
[straddleSet_card_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/EdgeUnique.lean)
-/
@[path]
private lemma straddleSet_card_le_one_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n) :
-- imply
  (straddleSet d a b).card ≤ 1 := by
-- proof
  apply StatMech.Onsager.EdgeUnique.straddleSet_card_le_one d hclosed hsimple hn a b

/--
[midSet_card_odd_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/EdgeUnique.lean)
-/
@[path]
private lemma midSet_card_odd_of_mem_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hk : k ∈ midSet d a b) :
-- imply
  (midSet d a b).card % 2 = 1 := by
-- proof
  apply StatMech.Onsager.EdgeUnique.midSet_card_odd_of_mem d hclosed hsimple hn a b k hk

/--
[straddleSet_card_odd_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/EdgeUnique.lean)
-/
@[path]
private lemma straddleSet_card_odd_of_mem_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {a b : ℤ}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hk : k ∈ straddleSet d a b) :
-- imply
  (straddleSet d a b).card % 2 = 1 := by
-- proof
  apply StatMech.Onsager.EdgeUnique.straddleSet_card_odd_of_mem d hclosed hsimple hn a b k hk


-- created on 2026-10-23
