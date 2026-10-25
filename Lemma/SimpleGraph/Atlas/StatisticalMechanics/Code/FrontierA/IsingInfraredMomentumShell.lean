import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredMomentumShell.Part2
open Finset Set StatMech StatMech.FrontierA


/--
[integerMomentumNormSq_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredMomentumShell.lean)
-/
@[path]
private lemma integerMomentumNormSq_nonneg_eq
  {d : Nat}
  {m : Site d} :
-- imply
  0 ≤ integerMomentumNormSq m := by
-- proof
  apply StatMech.FrontierA.integerMomentumNormSq_nonneg m

/--
[integerMomentumNormSq_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredMomentumShell.lean)
-/
@[path]
private lemma integerMomentumNormSq_pos_eq
  {d : Nat}
  {m : Site d}
-- given
  (hm : m ≠ 0) :
-- imply
  0 < integerMomentumNormSq m := by
-- proof
  apply StatMech.FrontierA.integerMomentumNormSq_pos hm

/--
[natCast_sq_le_integerMomentumNormSq_of_mem_shell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredMomentumShell.lean)
-/
@[path]
private lemma natCast_sq_le_integerMomentumNormSq_of_mem_shell_eq
  {d r : Nat}
  {m : Site d}
-- given
  (hr : 1 ≤ r)
  (hm : m ∈ boxSV_vbF d r) :
-- imply
  (r : Real) ^ 2 ≤ integerMomentumNormSq m := by
-- proof
  apply StatMech.FrontierA.natCast_sq_le_integerMomentumNormSq_of_mem_shell hr hm

/--
[sum_inv_integerMomentumNormSq_shell_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredMomentumShell.lean)
-/
@[path]
private lemma sum_inv_integerMomentumNormSq_shell_le_eq
  {d r : Nat}
-- given
  (hr : 1 ≤ r) :
-- imply
  ∑ m ∈ boxSV_vbF d r, (integerMomentumNormSq m)⁻¹ ≤ ((boxSV_vbF d r).card : Real) / (r : Real) ^ 2 := by
-- proof
  apply StatMech.FrontierA.sum_inv_integerMomentumNormSq_shell_le d r hr

/--
[integerMomentumShell_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredMomentumShell.lean)
-/
@[path]
private lemma integerMomentumShell_card_le_eq
  {d r : Nat}
-- given
  (hr : 1 ≤ r) :
-- imply
  ((boxSV_vbF d r).card : Real) ≤ 2 * d * (2 * (r : Real) + 1) ^ (d - 1) := by
-- proof
  apply StatMech.FrontierA.integerMomentumShell_card_le d r hr

/--
[sum_inv_integerMomentumNormSq_shell_le_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredMomentumShell.lean)
-/
@[path]
private lemma sum_inv_integerMomentumNormSq_shell_le_power_eq
  {d r : Nat}
-- given
  (hd : 3 ≤ d)
  (hr : 1 ≤ r) :
-- imply
  ∑ m ∈ boxSV_vbF d r, (integerMomentumNormSq m)⁻¹ ≤ 2 * d * 3 ^ (d - 1) * (r : Real) ^ (d - 3) := by
-- proof
  apply StatMech.FrontierA.sum_inv_integerMomentumNormSq_shell_le_power d r hd hr

/--
[integerMomentumBoxWithoutZero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredMomentumShell.lean)
-/
@[path]
private lemma integerMomentumBoxWithoutZero_succ_eq
  {d M : Nat} :
-- imply
  integerMomentumBoxWithoutZero d (M + 1) = integerMomentumBoxWithoutZero d M ∪ boxSV_vbF d (M + 1) := by
-- proof
  apply StatMech.FrontierA.integerMomentumBoxWithoutZero_succ d M

/--
[disjoint_integerMomentumBoxWithoutZero_shell_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredMomentumShell.lean)
-/
@[path]
private lemma disjoint_integerMomentumBoxWithoutZero_shell_succ_eq
  {d M : Nat} :
-- imply
  Disjoint (integerMomentumBoxWithoutZero d M) (boxSV_vbF d (M + 1)) := by
-- proof
  apply StatMech.FrontierA.disjoint_integerMomentumBoxWithoutZero_shell_succ d M

/--
[sum_inv_integerMomentumNormSq_box_eq_sum_shells](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredMomentumShell.lean)
-/
@[path]
private lemma sum_inv_integerMomentumNormSq_box_eq_sum_shells_eq
  {d M : Nat} :
-- imply
  ∑ m ∈ integerMomentumBoxWithoutZero d M, (integerMomentumNormSq m)⁻¹ = ∑ r ∈ Finset.range M, ∑ m ∈ boxSV_vbF d (r + 1), (integerMomentumNormSq m)⁻¹ := by
-- proof
  apply StatMech.FrontierA.sum_inv_integerMomentumNormSq_box_eq_sum_shells d M

/--
[sum_inv_integerMomentumNormSq_box_le_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredMomentumShell.lean)
-/
@[path]
private lemma sum_inv_integerMomentumNormSq_box_le_power_eq
  {d M : Nat}
-- given
  (hd : 3 ≤ d) :
-- imply
  ∑ m ∈ integerMomentumBoxWithoutZero d M, (integerMomentumNormSq m)⁻¹ ≤ 2 * d * 3 ^ (d - 1) * (M : Real) ^ (d - 2) := by
-- proof
  apply StatMech.FrontierA.sum_inv_integerMomentumNormSq_box_le_power d M hd


-- created on 2026-10-23
