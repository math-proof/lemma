import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
open StatMech StatMech.FrontierD


/--
[fkRectCriticalP_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean)
-/
@[path]
private lemma fkRectCriticalP_pos_eq
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  0 < fkRectCriticalP q := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalP_pos hq

/--
[fkRectCriticalP_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean)
-/
@[path]
private lemma fkRectCriticalP_lt_one_eq
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalP q < 1 := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalP_lt_one hq

/--
[one_sub_fkRectCriticalP](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean)
-/
@[path]
private lemma one_sub_fkRectCriticalP_eq
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  1 - fkRectCriticalP q = 1 / (1 + Real.sqrt q) := by
-- proof
  apply StatMech.FrontierD.one_sub_fkRectCriticalP hq

/--
[fkRectCriticalP_eq_sqrt_mul_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean)
-/
@[path]
private lemma fkRectCriticalP_eq_sqrt_mul_one_sub_eq
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalP q = Real.sqrt q * (1 - fkRectCriticalP q) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalP_eq_sqrt_mul_one_sub hq

/--
[card_fkRectEdgeIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean)
-/
@[path]
private lemma card_fkRectEdgeIndex_eq
  {R : FKRectTorus} :
-- imply
  Fintype.card R.EdgeIndex = 2 * R.width * R.height := by
-- proof
  apply StatMech.FrontierD.card_fkRectEdgeIndex R

/--
[fkRectEdgeProduct_critical_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean)
-/
@[path]
private lemma fkRectEdgeProduct_critical_eq_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  fkRectEdgeProduct R (fkRectCriticalP q) omega = (1 / (1 + Real.sqrt q)) ^ (2 * R.width * R.height) * Real.sqrt q ^ fkRectOpenEdgeCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectEdgeProduct_critical_eq R hq omega

/--
[fkRectRandomClusterWeight_critical_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean)
-/
@[path]
private lemma fkRectRandomClusterWeight_critical_eq_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  fkRectRandomClusterWeight R (fkRectCriticalP q) q omega = (1 / (1 + Real.sqrt q)) ^ (2 * R.width * R.height) * fkRectCriticalReducedWeight R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectRandomClusterWeight_critical_eq R hq omega

/--
[fkRectRandomClusterZ_critical_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean)
-/
@[path]
private lemma fkRectRandomClusterZ_critical_eq_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  fkRectRandomClusterZ R (fkRectCriticalP q) q = (1 / (1 + Real.sqrt q)) ^ (2 * R.width * R.height) * fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectRandomClusterZ_critical_eq R hq

/--
[fkRectCriticalReducedWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean)
-/
@[path]
private lemma fkRectCriticalReducedWeight_pos_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  0 < fkRectCriticalReducedWeight R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalReducedWeight_pos R hq omega

/--
[fkRectCriticalReducedZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean)
-/
@[path]
private lemma fkRectCriticalReducedZ_pos_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  0 < fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalReducedZ_pos R hq

/--
[fkRectCriticalRandomClusterProb_eq_weight_div_Z](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean)
-/
@[path]
private lemma fkRectCriticalRandomClusterProb_eq_weight_div_Z_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalRandomClusterProb R q omega = fkRectRandomClusterWeight R (fkRectCriticalP q) q omega / fkRectRandomClusterZ R (fkRectCriticalP q) q := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalRandomClusterProb_eq_weight_div_Z R hq omega

/--
[fkRectCriticalRandomClusterProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean)
-/
@[path]
private lemma fkRectCriticalRandomClusterProb_nonneg_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  0 <= fkRectCriticalRandomClusterProb R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalRandomClusterProb_nonneg R hq omega

/--
[sum_fkRectCriticalRandomClusterProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean)
-/
@[path]
private lemma sum_fkRectCriticalRandomClusterProb_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  ∑ omega : R.Configuration, fkRectCriticalRandomClusterProb R q omega = 1 := by
-- proof
  apply StatMech.FrontierD.sum_fkRectCriticalRandomClusterProb R hq

/--
[fkRectCriticalRandomClusterPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean)
-/
@[path]
private lemma fkRectCriticalRandomClusterPMF_apply_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalRandomClusterPMF R hq omega = ENNReal.ofReal (fkRectCriticalRandomClusterProb R q omega) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalRandomClusterPMF_apply R hq omega


-- created on 2026-10-23
