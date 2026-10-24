import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexCorrectedStripMasses
open StatMech StatMech.Universality


/--
[hexCSBoundaryClass_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMasses.lean)
-/
@[path]
private lemma hexCSBoundaryClass_reflect_eq
  {T L : ℕ}
  {e : HexCSIncidence T L} :
-- imply
  hexCSBoundaryClass (hexCSReflectIncidence e) = hexCSBoundaryClass e := by
-- proof
  apply StatMech.Universality.hexCSBoundaryClass_reflect e

/--
[hexCS_endpointCountObservable_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMasses.lean)
-/
@[path]
private lemma hexCS_endpointCountObservable_reflect_eq
  {T L : ℕ}
  {hT : 0 < T}
  {e : HexCSIncidence T L} :
-- imply
  endpointCountObservable (hexCSFiniteRegion T L hT).inRegion hexAWStart 1 (hexAWMid (hexCSReflectIncidence e).vtx.1 (hexCSReflectIncidence e).edge) hexChi = endpointCountObservable (hexCSFiniteRegion T L hT).inRegion hexAWStart 1 (hexAWMid e.vtx.1 e.edge) hexChi := by
-- proof
  apply StatMech.Universality.hexCS_endpointCountObservable_reflect e

/--
[hexCSIncidenceMass_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMasses.lean)
-/
@[path]
private lemma hexCSIncidenceMass_reflect_eq
  {T L : ℕ}
  {hT : 0 < T}
  {cls : HexPairedBoundaryClass}
  {e : HexCSIncidence T L} :
-- imply
  hexCSIncidenceMass T L hT cls (hexCSReflectIncidence e) = hexCSIncidenceMass T L hT cls e := by
-- proof
  apply StatMech.Universality.hexCSIncidenceMass_reflect cls e

/--
[hexCSFixedIndex_class_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMasses.lean)
-/
@[path]
private lemma hexCSFixedIndex_class_top_eq
  {T L : ℕ}
  {hT : 0 < T}
  {k : HexCSFixedIndex T L hT} :
-- imply
  hexCSBoundaryClass k.1 = .top := by
-- proof
  apply StatMech.Universality.hexCSFixedIndex_class_top k

/--
[hexCS_boundary_erase_start_eq_orbits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMasses.lean)
-/
@[path]
private lemma hexCS_boundary_erase_start_eq_orbits_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexCSBoundaryIncidences T L \ {hexCSStartIncidence T L hT} = Finset.univ.biUnion (hexCSOrbitPiece (T := T) (L := L) (hT := hT)) := by
-- proof
  apply StatMech.Universality.hexCS_boundary_erase_start_eq_orbits T L hT

/--
[hexCSLiteralBoundaryMass_eq_orbits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMasses.lean)
-/
@[path]
private lemma hexCSLiteralBoundaryMass_eq_orbits_eq
  {T L : ℕ}
  {cls : HexPairedBoundaryClass}
-- given
  (hT : 0 < T) :
-- imply
  hexCSLiteralBoundaryMass T L hT cls = (∑ i : HexCSPairIndex T L, if hexCSBoundaryClass i.1 = cls then 2 * endpointCountObservable (hexCSFiniteRegion T L hT).inRegion hexAWStart 1 (hexAWMid i.1.vtx.1 i.1.edge) hexChi else 0) + ∑ k : HexCSFixedIndex T L hT, if cls = .top then endpointCountObservable (hexCSFiniteRegion T L hT).inRegion hexAWStart 1 (hexAWMid k.1.vtx.1 k.1.edge) hexChi else 0 := by
-- proof
  apply StatMech.Universality.hexCSLiteralBoundaryMass_eq_orbits T L hT cls

/--
[hexCSA_eq_literalBoundaryMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMasses.lean)
-/
@[path]
private lemma hexCSA_eq_literalBoundaryMass_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexCSA T L hT = hexCSLiteralBoundaryMass T L hT .side := by
-- proof
  apply StatMech.Universality.hexCSA_eq_literalBoundaryMass T L hT

/--
[hexCSE_eq_literalBoundaryMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMasses.lean)
-/
@[path]
private lemma hexCSE_eq_literalBoundaryMass_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexCSE T L hT = hexCSLiteralBoundaryMass T L hT .slant := by
-- proof
  apply StatMech.Universality.hexCSE_eq_literalBoundaryMass T L hT

/--
[hexCSB_eq_literalBoundaryMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMasses.lean)
-/
@[path]
private lemma hexCSB_eq_literalBoundaryMass_eq
  {T L : ℕ}
-- given
  (hT : 0 < T) :
-- imply
  hexCSB T L hT = hexCSLiteralBoundaryMass T L hT .top := by
-- proof
  apply StatMech.Universality.hexCSB_eq_literalBoundaryMass T L hT


-- created on 2026-10-23
