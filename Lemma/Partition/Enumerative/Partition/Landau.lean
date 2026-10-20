import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.Landau
open Nat
open Partition


/--
[partsLCM_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Landau.lean)
-/
@[path]
private lemma partsLCM_zero_eq
  {p : Partition 0} :
-- imply
  p.partsLCM = 1 := by
-- proof
  apply Nat.Partition.partsLCM_zero p

/--
[partsLCM_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Landau.lean)
-/
@[path]
private lemma partsLCM_one_eq
  {p : Partition 1} :
-- imply
  p.partsLCM = 1 := by
-- proof
  apply Nat.Partition.partsLCM_one p

/--
[Partition.partsLCM_le_landauFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Landau.lean)
-/
@[path]
private lemma Partition_partsLCM_le_landauFunction_eq
  {n : ℕ}
  {p : n.Partition} :
-- imply
  p.partsLCM ≤ landauFunction n := by
-- proof
  apply Nat.Partition.partsLCM_le_landauFunction p

/--
[exists_partition_partsLCM_eq_landauFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Landau.lean)
-/
@[path]
private lemma exists_partition_partsLCM_eq_landauFunction_eq
  {n : ℕ} :
-- imply
  ∃ p : n.Partition, p.partsLCM = landauFunction n := by
-- proof
  apply Nat.exists_partition_partsLCM_eq_landauFunction n

/--
[landauFunction_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Landau.lean)
-/
@[path]
private lemma landauFunction_zero_eq
  :
-- imply
  landauFunction 0 = 1 := by
-- proof
  apply Nat.landauFunction_zero

/--
[landauFunction_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Landau.lean)
-/
@[path]
private lemma landauFunction_one_eq
  :
-- imply
  landauFunction 1 = 1 := by
-- proof
  apply Nat.landauFunction_one


-- created on 2026-10-20
