import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectCriticalDualQuasiInvariant
open StatMech StatMech.FrontierD


/--
[fkRectMedialLoopCount_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean)
-/
@[path]
private lemma fkRectMedialLoopCount_dual_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectMedialLoopCount R (fkRectDualConfigurationEquiv R omega) = fkRectMedialLoopCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectMedialLoopCount_dual R omega

/--
[fkRectCriticalReducedWeight_eq_loop_net](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean)
-/
@[path]
private lemma fkRectCriticalReducedWeight_eq_loop_net_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalReducedWeight R q omega = Real.sqrt q ^ (R.width * R.height : Nat) * Real.sqrt q ^ fkRectMedialLoopCount R omega * q ^ fkRectNetIndicator R omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalReducedWeight_eq_loop_net R hq omega

/--
[fkRectCriticalReducedWeight_dual_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean)
-/
@[path]
private lemma fkRectCriticalReducedWeight_dual_le_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalReducedWeight R q (fkRectDualConfigurationEquiv R omega) ≤ q * fkRectCriticalReducedWeight R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalReducedWeight_dual_le R hq omega

/--
[fkRectCriticalReducedWeight_le_q_mul_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean)
-/
@[path]
private lemma fkRectCriticalReducedWeight_le_q_mul_dual_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalReducedWeight R q omega ≤ q * fkRectCriticalReducedWeight R q (fkRectDualConfigurationEquiv R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalReducedWeight_le_q_mul_dual R hq omega

/--
[fkRectCriticalRandomClusterProb_dual_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean)
-/
@[path]
private lemma fkRectCriticalRandomClusterProb_dual_le_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalRandomClusterProb R q (fkRectDualConfigurationEquiv R omega) ≤ q * fkRectCriticalRandomClusterProb R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalRandomClusterProb_dual_le R hq omega

/--
[fkRectCriticalRandomClusterProb_le_q_mul_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean)
-/
@[path]
private lemma fkRectCriticalRandomClusterProb_le_q_mul_dual_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalRandomClusterProb R q omega ≤ q * fkRectCriticalRandomClusterProb R q (fkRectDualConfigurationEquiv R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalRandomClusterProb_le_q_mul_dual R hq omega

/--
[fkRectDualPreimageEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean)
-/
@[path]
private lemma fkRectDualPreimageEvent_isIncreasing_eq
  {R : FKRectTorus}
  {A : Set R.Configuration}
-- given
  (hA : IsDecreasing A) :
-- imply
  IsIncreasing (fkRectDualPreimageEvent R A) := by
-- proof
  apply StatMech.FrontierD.fkRectDualPreimageEvent_isIncreasing R hA

/--
[fkRectDualEvent_dualPreimageEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean)
-/
@[path]
private lemma fkRectDualEvent_dualPreimageEvent_eq
  {R : FKRectTorus}
  {A : Set R.Configuration} :
-- imply
  fkRectDualEvent R (fkRectDualPreimageEvent R A) = A := by
-- proof
  apply StatMech.FrontierD.fkRectDualEvent_dualPreimageEvent R A

/--
[fkRectCriticalEventMass_dualEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_dualEvent_eq_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration} :
-- imply
  fkRectCriticalEventMass R q (fkRectDualEvent R A) = ∑ omega : R.Configuration, A.indicator (fun omega => fkRectCriticalRandomClusterProb R q (fkRectDualConfigurationEquiv R omega)) omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_dualEvent_eq R q A

/--
[fkRectCriticalEventMass_dualEvent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_dualEvent_le_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalEventMass R q (fkRectDualEvent R A) ≤ q * fkRectCriticalEventMass R q A := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_dualEvent_le R hq A

/--
[fkRectCriticalEventMass_le_q_mul_dualEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_le_q_mul_dualEvent_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalEventMass R q A ≤ q * fkRectCriticalEventMass R q (fkRectDualEvent R A) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_le_q_mul_dualEvent R hq A

/--
[one_div_q_mul_eventMass_le_of_dualEvent_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean)
-/
@[path]
private lemma one_div_q_mul_eventMass_le_of_dualEvent_subset_eq
  {R : FKRectTorus}
  {q : Real}
  {A B : Set R.Configuration}
-- given
  (hq : 1 <= q)
  (hAB : fkRectDualEvent R A ⊆ B) :
-- imply
  (1 / q) * fkRectCriticalEventMass R q A <= fkRectCriticalEventMass R q B := by
-- proof
  apply StatMech.FrontierD.one_div_q_mul_eventMass_le_of_dualEvent_subset R hq hAB

/--
[one_div_one_add_q_le_eventMass_of_compl_subset_dualEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean)
-/
@[path]
private lemma one_div_one_add_q_le_eventMass_of_compl_subset_dualEvent_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 1 ≤ q)
  (hcover : Aᶜ ⊆ fkRectDualEvent R A) :
-- imply
  1 / (1 + q) ≤ fkRectCriticalEventMass R q A := by
-- proof
  apply StatMech.FrontierD.one_div_one_add_q_le_eventMass_of_compl_subset_dualEvent R hq A hcover

/--
[one_div_one_add_q_le_eventMass_of_dualCompl_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalDualQuasiInvariant.lean)
-/
@[path]
private lemma one_div_one_add_q_le_eventMass_of_dualCompl_subset_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 1 ≤ q)
  (hcover : fkRectDualEvent R Aᶜ ⊆ A) :
-- imply
  1 / (1 + q) ≤ fkRectCriticalEventMass R q A := by
-- proof
  apply StatMech.FrontierD.one_div_one_add_q_le_eventMass_of_dualCompl_subset R hq A hcover


-- created on 2026-10-23
