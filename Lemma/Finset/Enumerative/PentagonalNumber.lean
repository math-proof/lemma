import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.PentagonalNumber
open scoped BigOperators
open scoped PowerSeries.WithPiTopology
open MetaMathlibExt


/--
[partitionFunction_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PentagonalNumber.lean)
-/
@[path]
private lemma partitionFunction_zero_eq
  :
-- imply
  partitionFunction 0 = 1 := by
-- proof
  apply MetaMathlibExt.partitionFunction_zero

/--
[partitionFunction_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PentagonalNumber.lean)
-/
@[path]
private lemma partitionFunction_one_eq
  :
-- imply
  partitionFunction 1 = 1 := by
-- proof
  apply MetaMathlibExt.partitionFunction_one

/--
[mk_partitionFunction_eq_genFun](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PentagonalNumber.lean)
-/
@[path]
private lemma mk_partitionFunction_eq_genFun_eq
  :
-- imply
  PowerSeries.mk (fun n => ((partitionFunction n : ℕ) : ℤ))
    = Nat.Partition.genFun (fun _ _ => (1 : ℤ)) := by
-- proof
  apply MetaMathlibExt.mk_partitionFunction_eq_genFun

/--
[mk_partitionFunction_mul_pentagonalSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PentagonalNumber.lean)
-/
@[path]
private lemma mk_partitionFunction_mul_pentagonalSeries_eq
  :
-- imply
  PowerSeries.mk (fun n => ((partitionFunction n : ℕ) : ℤ)) *
    PowerSeries.pentagonalSeries ℤ = 1 := by
-- proof
  apply MetaMathlibExt.mk_partitionFunction_mul_pentagonalSeries

/--
[pentagonal_number_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PentagonalNumber.lean)
-/
@[path]
private lemma pentagonal_number_theorem_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  (partitionFunction n : ℤ) =
    ∑ m ∈ Finset.filter (fun m : ℕ => 1 ≤ m) (Finset.range (n + 1)),
    (((-1 : ℤ) ^ (m + 1) *
    (if pentagonal (m : ℤ) ≤ n
    then (partitionFunction (n - pentagonal (m : ℤ)) : ℤ)
    else 0)) +
    ((-1 : ℤ) ^ (m + 1) *
    (if pentagonal (-(m : ℤ)) ≤ n
    then (partitionFunction (n - pentagonal (-(m : ℤ))) : ℤ)
    else 0))) := by
-- proof
  apply MetaMathlibExt.pentagonal_number_theorem n hn


-- created on 2026-10-20
