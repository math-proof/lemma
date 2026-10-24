import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexCorrectedStripMassLimits
open StatMech StatMech.Universality


/--
[hexCSClassWalkMass_eq_predicateMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMassLimits.lean)
-/
@[path]
private lemma hexCSClassWalkMass_eq_predicateMass_eq
  {T L : ℕ}
  {cls : HexPairedBoundaryClass}
-- given
  (hT : 0 < T) :
-- imply
  hexCSClassWalkMass T L hT cls = hexCSPredicateMass (HexCSClassWalk T L hT cls) := by
-- proof
  apply StatMech.Universality.hexCSClassWalkMass_eq_predicateMass T L hT cls

/--
[hexCSA_eq_sideWalkMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMassLimits.lean)
-/
@[path]
private lemma hexCSA_eq_sideWalkMass_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexCSA T L hT = hexCSPredicateMass (HexCSSideWalk T L hT) := by
-- proof
  apply StatMech.Universality.hexCSA_eq_sideWalkMass T L hT

/--
[hexCSE_eq_slantWalkMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMassLimits.lean)
-/
@[path]
private lemma hexCSE_eq_slantWalkMass_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexCSE T L hT = hexCSPredicateMass (HexCSSlantWalk T L hT) := by
-- proof
  apply StatMech.Universality.hexCSE_eq_slantWalkMass T L hT

/--
[hexCSB_eq_topWalkMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMassLimits.lean)
-/
@[path]
private lemma hexCSB_eq_topWalkMass_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexCSB T L hT = hexCSPredicateMass (HexCSTopWalk T L hT) := by
-- proof
  apply StatMech.Universality.hexCSB_eq_topWalkMass T L hT

/--
[hexCSPredicateMass_tendsto_of_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMassLimits.lean)
-/
@[path]
private lemma hexCSPredicateMass_tendsto_of_dominated_eq
-- given
  (P : ℕ → List ℤ → Prop)
  (Pinf : List ℤ → Prop)
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE))
  (hlegal : ∀ L ts, P L ts → (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
  (hpoint : ∀ ts, Tendsto (fun L => hexCSPredicateWeight (P L) ts) atTop (nhds (hexCSPredicateWeight Pinf ts))) :
-- imply
  Tendsto (fun L => hexCSPredicateMass (P L)) atTop (nhds (hexCSPredicateMass Pinf)) := by
-- proof
  apply StatMech.Universality.hexCSPredicateMass_tendsto_of_dominated P Pinf hwalk hlegal hpoint

/--
[hexCSSideMass_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMassLimits.lean)
-/
@[path]
private lemma hexCSSideMass_tendsto_eq
  {T : ℕ}
-- given
  (hT : 0 < T)
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  Tendsto (fun L => hexCSPredicateMass (HexCSSideWalk T L hT)) atTop (nhds (hexCSPredicateMass (HexCSSideWalkAtWidth T hT))) := by
-- proof
  apply StatMech.Universality.hexCSSideMass_tendsto T hT hwalk

/--
[hexCSTopMass_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMassLimits.lean)
-/
@[path]
private lemma hexCSTopMass_tendsto_eq
  {T : ℕ}
-- given
  (hT : 0 < T)
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  Tendsto (fun L => hexCSPredicateMass (HexCSTopWalk T L hT)) atTop (nhds (hexCSPredicateMass (HexCSTopWalkAtWidth T hT))) := by
-- proof
  apply StatMech.Universality.hexCSTopMass_tendsto T hT hwalk

/--
[hexCSSlantMass_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMassLimits.lean)
-/
@[path]
private lemma hexCSSlantMass_tendsto_zero_eq
  {T : ℕ}
-- given
  (hT : 0 < T)
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  Tendsto (fun L => hexCSPredicateMass (HexCSSlantWalk T L hT)) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.hexCSSlantMass_tendsto_zero T hT hwalk

/--
[hexCSA_tendsto_infiniteHeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMassLimits.lean)
-/
@[path]
private lemma hexCSA_tendsto_infiniteHeight_eq
  {T : ℕ}
-- given
  (hT : 0 < T)
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  Tendsto (fun L => hexCSA T L hT) atTop (nhds (hexCSPredicateMass (HexCSSideWalkAtWidth T hT))) := by
-- proof
  apply StatMech.Universality.hexCSA_tendsto_infiniteHeight T hT hwalk

/--
[hexCSB_tendsto_infiniteHeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMassLimits.lean)
-/
@[path]
private lemma hexCSB_tendsto_infiniteHeight_eq
  {T : ℕ}
-- given
  (hT : 0 < T)
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  Tendsto (fun L => hexCSB T L hT) atTop (nhds (hexCSPredicateMass (HexCSTopWalkAtWidth T hT))) := by
-- proof
  apply StatMech.Universality.hexCSB_tendsto_infiniteHeight T hT hwalk

/--
[hexCSE_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMassLimits.lean)
-/
@[path]
private lemma hexCSE_tendsto_zero_eq
  {T : ℕ}
-- given
  (hT : 0 < T)
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  Tendsto (fun L => hexCSE T L hT) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.hexCSE_tendsto_zero T hT hwalk

/--
[hexCS_infiniteHeight_boundary_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMassLimits.lean)
-/
@[path]
private lemma hexCS_infiniteHeight_boundary_identity_eq
  {T : ℕ}
-- given
  (hT : 0 < T)
  (hfinite : ∀ L, hexCl * hexCSA T L hT + hexCt * hexCSE T L hT + hexCSB T L hT = 1)
  (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
-- imply
  hexCl * hexCSPredicateMass (HexCSSideWalkAtWidth T hT) + hexCSPredicateMass (HexCSTopWalkAtWidth T hT) = 1 := by
-- proof
  apply StatMech.Universality.hexCS_infiniteHeight_boundary_identity T hT hfinite hwalk


-- created on 2026-10-23
