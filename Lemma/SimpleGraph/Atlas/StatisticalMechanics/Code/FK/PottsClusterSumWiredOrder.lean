import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PottsClusterSumWiredOrder
open MeasureTheory Set StatMech StatMech.FK


/--
[pottsIIDLabelMeasure_clusterSumSpin_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredOrder.lean)
-/
@[path]
private lemma pottsIIDLabelMeasure_clusterSumSpin_apply_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor a : Fin q}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  pottsIIDLabelMeasure d q {label | pottsClusterSumSpin boundaryColor omega label x = a} = if (cluster d omega x).Infinite then if boundaryColor = a then 1 else 0 else (q : ENNReal)⁻¹ := by
-- proof
  apply StatMech.FK.pottsIIDLabelMeasure_clusterSumSpin_apply boundaryColor a omega x

/--
[pottsClusterSumJointMeasure_boundaryColor_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredOrder.lean)
-/
@[path]
private lemma pottsClusterSumJointMeasure_boundaryColor_apply_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {edgeMeasure : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure edgeMeasure]
  {x : Site d} :
-- imply
  Measure.map Prod.fst (pottsClusterSumJointMeasure boundaryColor edgeMeasure) (pottsColorEvent d q x boundaryColor) = edgeMeasure {omega | (cluster d omega x).Infinite} + (q : ENNReal)⁻¹ * edgeMeasure {omega | (cluster d omega x).Finite} := by
-- proof
  apply StatMech.FK.pottsClusterSumJointMeasure_boundaryColor_apply boundaryColor edgeMeasure x

/--
[pottsClusterSumJointMeasure_otherColor_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredOrder.lean)
-/
@[path]
private lemma pottsClusterSumJointMeasure_otherColor_apply_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor a : Fin q}
  {edgeMeasure : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure edgeMeasure]
  {x : Site d}
-- given
  (hba : boundaryColor ≠ a) :
-- imply
  Measure.map Prod.fst (pottsClusterSumJointMeasure boundaryColor edgeMeasure) (pottsColorEvent d q x a) = (q : ENNReal)⁻¹ * edgeMeasure {omega | (cluster d omega x).Finite} := by
-- proof
  apply StatMech.FK.pottsClusterSumJointMeasure_otherColor_apply boundaryColor a hba edgeMeasure x

/--
[pottsClusterSumJointMeasure_boundaryColor_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredOrder.lean)
-/
@[path]
private lemma pottsClusterSumJointMeasure_boundaryColor_real_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {edgeMeasure : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure edgeMeasure]
  {x : Site d} :
-- imply
  (Measure.map Prod.fst (pottsClusterSumJointMeasure boundaryColor edgeMeasure)).real (pottsColorEvent d q x boundaryColor) = edgeMeasure.real {omega | (cluster d omega x).Infinite} + (1 / (q : Real)) * edgeMeasure.real {omega | (cluster d omega x).Finite} := by
-- proof
  apply StatMech.FK.pottsClusterSumJointMeasure_boundaryColor_real boundaryColor edgeMeasure x

/--
[wiredPottsClusterSum_boundaryColorBias_eq_fkTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredOrder.lean)
-/
@[path]
private lemma wiredPottsClusterSum_boundaryColorBias_eq_fkTheta_eq
  {d q : Nat}
  [NeZero q]
  {boundaryColor : Fin q}
  {p : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q) (Measure.map Prod.fst (pottsClusterSumJointMeasure boundaryColor (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _))).real (pottsColorEvent d q (origin d) boundaryColor) - 1 / (q : Real) = ((q : Real) - 1) / q * fkTheta d hp hp1 (zero_lt_one.trans_le hqR) (q := q) := by
-- proof
  apply StatMech.FK.wiredPottsClusterSum_boundaryColorBias_eq_fkTheta boundaryColor hp hp1


-- created on 2026-10-23
