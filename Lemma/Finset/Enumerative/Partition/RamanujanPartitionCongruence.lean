import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence
open MathlibExt
open MetaMathlibExt


/--
[two_mul_choose_two_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruence.lean)
-/
@[path]
private lemma two_mul_choose_two_succ_eq
  {a : ℕ} :
-- imply
  2 * (a + 1).choose 2 = a * (a + 1) := by
-- proof
  apply MetaMathlibExt.two_mul_choose_two_succ a

/--
[coeff_jacobiCubeSeries_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruence.lean)
-/
@[path]
private lemma coeff_jacobiCubeSeries_triangle_eq
  {t : ℕ} :
-- imply
  PowerSeries.coeff ((t + 1).choose 2) jacobiCubeSeries = (-1 : ℤ) ^ t * (2 * t + 1) := by
-- proof
  apply MetaMathlibExt.coeff_jacobiCubeSeries_triangle t

/--
[coeff_jacobiCubeSeries_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruence.lean)
-/
@[path]
private lemma coeff_jacobiCubeSeries_eq_zero_eq
  {b : ℕ}
-- given
  (hb : ∀ t : ℕ, (t + 1).choose 2 ≠ b) :
-- imply
  PowerSeries.coeff b jacobiCubeSeries = 0 := by
-- proof
  apply MetaMathlibExt.coeff_jacobiCubeSeries_eq_zero hb

/--
[pentagonalSeries_pow_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruence.lean)
-/
@[path]
private lemma pentagonalSeries_pow_three_eq
  :
-- imply
  PowerSeries.pentagonalSeries ℤ ^ 3 = jacobiCubeSeries := by
-- proof
  apply MetaMathlibExt.pentagonalSeries_pow_three

/--
[dvd_partitionFunction_of_dvd_coeff_pentagonalSeries_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruence.lean)
-/
@[path]
private lemma dvd_partitionFunction_of_dvd_coeff_pentagonalSeries_pow_eq
  {p r : ℕ} [Fact (Nat.Prime p)]
  {m : ℕ}
-- given
  (hr : r < p)
  (hvan : ∀ m : ℕ, (p : ℤ) ∣ PowerSeries.coeff (p * m + r) (PowerSeries.pentagonalSeries ℤ ^ (p - 1))) :
-- imply
  p ∣ Fintype.card (Nat.Partition (p * m + r)) := by
-- proof
  apply MetaMathlibExt.dvd_partitionFunction_of_dvd_coeff_pentagonalSeries_pow p r hr hvan m

/--
[ramanujan_partition_congruence_mod_five](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruence.lean)
-/
@[path]
private lemma ramanujan_partition_congruence_mod_five_eq
  {m : ℕ} :
-- imply
  Fintype.card (Nat.Partition (5 * m + 4)) ≡ 0 [MOD 5] := by
-- proof
  apply MetaMathlibExt.ramanujan_partition_congruence_mod_five m

/--
[ramanujan_partition_congruence_mod_seven](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruence.lean)
-/
@[path]
private lemma ramanujan_partition_congruence_mod_seven_eq
  {m : ℕ} :
-- imply
  Fintype.card (Nat.Partition (7 * m + 5)) ≡ 0 [MOD 7] := by
-- proof
  apply MetaMathlibExt.ramanujan_partition_congruence_mod_seven m


-- created on 2026-10-20
