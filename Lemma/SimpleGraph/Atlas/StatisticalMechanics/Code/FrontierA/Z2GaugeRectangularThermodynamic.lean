import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeRectangularThermodynamic
open Filter Set Topology StatMech StatMech.FrontierA


/--
[cubicalRectangularWilsonFreeEnergy_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeRectangularThermodynamic.lean)
-/
@[path]
private lemma cubicalRectangularWilsonFreeEnergy_nonneg_eq
  {beta : Real}
  {m n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  0 <= cubicalRectangularWilsonFreeEnergy beta m n := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonFreeEnergy_nonneg hbeta m n

/--
[cubicalRectangularWilsonFreeEnergy_eq_disorderFreeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeRectangularThermodynamic.lean)
-/
@[path]
private lemma cubicalRectangularWilsonFreeEnergy_eq_disorderFreeEnergy_eq
  {beta : Real}
  {m n : Nat}
-- given
  (hbeta : 0 < beta)
  (hm : 0 < m)
  (hn : 0 < n) :
-- imply
  cubicalRectangularWilsonFreeEnergy beta m n = cubicalRectangularDisorderFreeEnergy beta m n := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonFreeEnergy_eq_disorderFreeEnergy hbeta hm hn

/--
[cubicalRectangularWilsonFreeEnergy_succ_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeRectangularThermodynamic.lean)
-/
@[path]
private lemma cubicalRectangularWilsonFreeEnergy_succ_self_eq
  {beta : Real}
  {n : Nat} :
-- imply
  cubicalRectangularWilsonFreeEnergy beta (n + 1) (n + 1) = cubicalSquareWilsonFreeEnergy beta n := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonFreeEnergy_succ_self beta n

/--
[cubicalSquareWilsonDensity_tendsto_rectangularSurfaceRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeRectangularThermodynamic.lean)
-/
@[path]
private lemma cubicalSquareWilsonDensity_tendsto_rectangularSurfaceRate_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hglue : HasRectangularBlockGluing (cubicalRectangularWilsonFreeEnergy beta)) :
-- imply
  Tendsto (cubicalSquareWilsonDensity beta) atTop (nhds (rectangularSurfaceRate (cubicalRectangularWilsonFreeEnergy beta))) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilsonDensity_tendsto_rectangularSurfaceRate hbeta hglue

/--
[cubicalSquareDisorderDensity_tendsto_rectangularSurfaceRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeRectangularThermodynamic.lean)
-/
@[path]
private lemma cubicalSquareDisorderDensity_tendsto_rectangularSurfaceRate_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hglue : HasRectangularBlockGluing (cubicalRectangularWilsonFreeEnergy beta)) :
-- imply
  Tendsto (cubicalSquareDisorderDensity beta) atTop (nhds (rectangularSurfaceRate (cubicalRectangularWilsonFreeEnergy beta))) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareDisorderDensity_tendsto_rectangularSurfaceRate hbeta hglue


-- created on 2026-10-23
