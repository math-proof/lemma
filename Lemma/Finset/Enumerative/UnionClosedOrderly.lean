import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.UnionClosedOrderly
open MetaMathlibExt


/--
[setLT_iff_setKey_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/UnionClosedOrderly.lean)
-/
@[path]
private lemma setLT_iff_setKey_lt_eq
  {n : ℕ}
  {A B : Finset (Fin n)} :
-- imply
  setLT n A B ↔ setKey n A < setKey n B := by
-- proof
  apply MetaMathlibExt.setLT_iff_setKey_lt n A B

/--
[orderly_canonical_prefix_of_sorted](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/UnionClosedOrderly.lean)
-/
@[path]
private lemma orderly_canonical_prefix_of_sorted_eq
  {n k m : ℕ}
  {U : Finset (Finset (Fin n))}
  {A : Fin k → Finset (Fin n)}
-- given
  (hmk : m ≤ k)
  (hU : U = insert ∅ (Finset.image A Finset.univ))
  (hne : ∀ i, A i ≠ ∅)
  (hlt : ∀ i j : Fin k, i < j → setLT n (A i) (A j))
  (hcan : IsCanonical n U) :
-- imply
  IsCanonical n
    (insert ∅ (Finset.image (fun i : Fin m => A (Fin.castLE hmk i)) Finset.univ)) := by
-- proof
  apply MetaMathlibExt.orderly_canonical_prefix_of_sorted n k m U A hmk hU hne hlt hcan

/--
[orderly_canonical_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/UnionClosedOrderly.lean)
-/
@[path]
private lemma orderly_canonical_prefix_eq
  {n k m : ℕ}
  {U : Finset (Finset (Fin n))}
  {A : Fin k → Finset (Fin n)}
-- given
  (hm : 1 ≤ m)
  (hmk : m ≤ k)
  (hU : U = insert ∅ (Finset.image A Finset.univ))
  (hne : ∀ i, A i ≠ ∅)
  (hlt : ∀ i j : Fin k, i < j → setLT n (A i) (A j))
  (hbase : U ≠ {Finset.univ, ∅})
  (hcov : ∀ i : Fin n, ∃ A₀ ∈ U, i ∈ A₀)
  (huc : IsUnionClosed n U)
  (hcan : IsCanonical n U) :
-- imply
  IsCanonical n
    (insert ∅ (Finset.image (fun i : Fin m => A (Fin.castLE hmk i)) Finset.univ)) := by
-- proof
  apply MetaMathlibExt.orderly_canonical_prefix n k m U A hm hmk hU hne hlt hbase hcov huc hcan


-- created on 2026-10-20
