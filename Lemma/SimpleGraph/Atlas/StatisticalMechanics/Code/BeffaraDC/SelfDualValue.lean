import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
open Real StatMech StatMech.BeffaraDC


/--
[dualDen_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SelfDualValue.lean)
-/
@[path]
private lemma dualDen_pos_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < (1 - p) * q + p := by
-- proof
  apply StatMech.BeffaraDC.dualDen_pos hp hp1 hq

/--
[dualParam_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SelfDualValue.lean)
-/
@[path]
private lemma dualParam_pos_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < dualParam p q := by
-- proof
  apply StatMech.BeffaraDC.dualParam_pos hp hp1 hq

/--
[dualParam_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SelfDualValue.lean)
-/
@[path]
private lemma dualParam_lt_one_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  dualParam p q < 1 := by
-- proof
  apply StatMech.BeffaraDC.dualParam_lt_one hp hp1 hq

/--
[dualParam_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SelfDualValue.lean)
-/
@[path]
private lemma dualParam_mem_Ioo_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  dualParam p q ∈ Set.Ioo (0 : ℝ) 1 := by
-- proof
  apply StatMech.BeffaraDC.dualParam_mem_Ioo hp hp1 hq

/--
[dualParam_product_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SelfDualValue.lean)
-/
@[path]
private lemma dualParam_product_eq_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (dualParam p q) * p / ((1 - dualParam p q) * (1 - p)) = q := by
-- proof
  apply StatMech.BeffaraDC.dualParam_product_eq hp hp1 hq

/--
[dualParam_fixed_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SelfDualValue.lean)
-/
@[path]
private lemma dualParam_fixed_iff_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  dualParam p q = p ↔ p ^ 2 = q * (1 - p) ^ 2 := by
-- proof
  apply StatMech.BeffaraDC.dualParam_fixed_iff hp hp1 hq

/--
[selfDualPoint_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SelfDualValue.lean)
-/
@[path]
private lemma selfDualPoint_mem_Ioo_eq
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  selfDualPoint q ∈ Set.Ioo (0 : ℝ) 1 := by
-- proof
  apply StatMech.BeffaraDC.selfDualPoint_mem_Ioo hq

/--
[selfDualPoint_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SelfDualValue.lean)
-/
@[path]
private lemma selfDualPoint_sq_eq
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  (selfDualPoint q) ^ 2 = q * (1 - selfDualPoint q) ^ 2 := by
-- proof
  apply StatMech.BeffaraDC.selfDualPoint_sq hq

/--
[selfDualPoint_is_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SelfDualValue.lean)
-/
@[path]
private lemma selfDualPoint_is_fixed_eq
  {q : ℝ}
-- given
  (hq : 0 < q) :
-- imply
  dualParam (selfDualPoint q) q = selfDualPoint q := by
-- proof
  apply StatMech.BeffaraDC.selfDualPoint_is_fixed hq

/--
[selfDualPoint_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SelfDualValue.lean)
-/
@[path]
private lemma selfDualPoint_unique_eq
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hfix : dualParam p q = p) :
-- imply
  p = selfDualPoint q := by
-- proof
  apply StatMech.BeffaraDC.selfDualPoint_unique hp hp1 hq hfix


-- created on 2026-10-23
