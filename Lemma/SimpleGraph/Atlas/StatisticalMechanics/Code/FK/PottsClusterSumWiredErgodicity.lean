import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredErgodicity
open MeasureTheory ProbabilityTheory Set Filter Topology StatMech StatMech.FK


/--
[wiredInfiniteVolume_axisShift_ergodic_generalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredErgodicity.lean)
-/
@[path]
private lemma wiredInfiniteVolume_axisShift_ergodic_generalQ_eq
  {d : Nat}
  {p q : Real}
-- given
  (hd : 1 <= d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  _root_.Ergodic (ConfigSpace.shift (freeAxisTranslation hd) : ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d))) (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
-- proof
  apply StatMech.FK.wiredInfiniteVolume_axisShift_ergodic_generalQ hd hp hp1 hq

/--
[wiredInfiniteVolume_prod_pottsIIDLabel_axis_ergodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredErgodicity.lean)
-/
@[path]
private lemma wiredInfiniteVolume_prod_pottsIIDLabel_axis_ergodic_eq
  {d q : Nat}
  [NeZero q]
  {p : Real}
-- given
  (hd : 1 <= d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q) _root_.Ergodic (Prod.map (ConfigSpace.shift (freeAxisTranslation hd) : ConfigSpace (Sym2 (Site d)) -> ConfigSpace (Sym2 (Site d))) (pottsLabelShift (freeAxisTranslation hd))) ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _).prod (pottsIIDLabelMeasure d q)) := by
-- proof
  apply StatMech.FK.wiredInfiniteVolume_prod_pottsIIDLabel_axis_ergodic hd hp hp1

/--
[wiredInfiniteVolume_pottsClusterFactorInput_isErgodicFor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredErgodicity.lean)
-/
@[path]
private lemma wiredInfiniteVolume_pottsClusterFactorInput_isErgodicFor_eq
  {d q : Nat}
  [NeZero q]
  {p : Real}
-- given
  (hd : 1 <= d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q) IsErgodicFor pottsClusterFactorInputShift ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _).prod (pottsIIDLabelMeasure d q)) := by
-- proof
  apply StatMech.FK.wiredInfiniteVolume_pottsClusterFactorInput_isErgodicFor hd hp hp1

/--
[wiredPottsClusterSumJointMeasure_isErgodicFor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredErgodicity.lean)
-/
@[path]
private lemma wiredPottsClusterSumJointMeasure_isErgodicFor_eq
  {d q : Nat}
  [NeZero q]
  {p : Real}
  {boundaryColor : Fin q}
-- given
  (hd : 1 <= d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q) IsErgodicFor (pottsJointShift (d := d) (q := q)) (pottsClusterSumJointMeasure (d := d) (q := q) boundaryColor (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _)) := by
-- proof
  apply StatMech.FK.wiredPottsClusterSumJointMeasure_isErgodicFor hd hp hp1 boundaryColor

/--
[wiredPottsClusterSumSpinMarginal_isErgodicFor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredErgodicity.lean)
-/
@[path]
private lemma wiredPottsClusterSumSpinMarginal_isErgodicFor_eq
  {d q : Nat}
  [NeZero q]
  {p : Real}
  {boundaryColor : Fin q}
-- given
  (hd : 1 <= d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  let hqR : (1 : Real) <= q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q) IsErgodicFor (pottsSpinShift (d := d) (q := q)) (Measure.map Prod.fst (pottsClusterSumJointMeasure (d := d) (q := q) boundaryColor (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hqR) : Measure _))) := by
-- proof
  apply StatMech.FK.wiredPottsClusterSumSpinMarginal_isErgodicFor hd hp hp1 boundaryColor


-- created on 2026-10-23
