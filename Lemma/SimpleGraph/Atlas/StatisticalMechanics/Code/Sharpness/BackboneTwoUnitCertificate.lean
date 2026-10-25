import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoUnitCertificate
open SimpleGraph Finset StatMech StatMech.Sharpness StatMech.Sharpness.BackboneTwoUnitCertificate


/--
[twoUnit_canonicalToggle_instance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoUnitCertificate.lean)
-/
@[path]
private lemma twoUnit_canonicalToggle_instance_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f)
  (hfirst : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit (twoUnitFlux d.graph e f) b) ⟨d, []⟩ = some e.1)
  (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  ∃ path : Finset (Copy d.graph (twoUnitFlux d.graph e f)), ∀ T, BondwisePairEvent ((program (V := V)).runSpec d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)) d.graph (twoUnitFlux d.graph e f) T <-> BondwisePairEvent (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE) ((program (V := V)).liftedResidualRunSpec d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]) d.graph (twoUnitFlux d.graph e f) (T ∆ path) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoUnitCertificate.twoUnit_canonicalToggle_instance d e f hne hfirst hactiveE hactiveF hpath

/--
[sources_secondCopy_eq_stepToggleSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoUnitCertificate.lean)
-/
@[path]
private lemma sources_secondCopy_eq_stepToggleSource_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  RandomCurrent.sources (endsM d.graph (twoUnitFlux d.graph e f)) ({secondCopy d.graph e f hne} : Finset (Copy d.graph (twoUnitFlux d.graph e f))) = stepToggleSource (selectorSpec (V := V)).toPartialSelector d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f] := by
-- proof
  apply StatMech.Sharpness.BackboneTwoUnitCertificate.sources_secondCopy_eq_stepToggleSource d e f hne

/--
[weight_twoUnitFlux_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoUnitCertificate.lean)
-/
@[path]
private lemma weight_twoUnitFlux_pos_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 < beta)
  (hJ : ∀ g, 0 < J g) :
-- imply
  0 < weight d.graph beta J (ofEdgeFun d.graph (twoUnitFlux d.graph e f)) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoUnitCertificate.weight_twoUnitFlux_pos beta J hbeta hJ d e f

/--
[twoUnit_left_rawPairFiberMass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoUnitCertificate.lean)
-/
@[path]
private lemma twoUnit_left_rawPairFiberMass_pos_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 < beta)
  (hJ : ∀ g, 0 < J g)
  (hne : e ≠ f)
  (hfirst : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit (twoUnitFlux d.graph e f) b) ⟨d, []⟩ = some e.1)
  (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  0 < rawSourcePairFiberMass d.graph beta J (twoUnitFlux d.graph e f) ((selectorSpec (V := V)).toPartialSelector.sourceClass d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) ((selectorSpec (V := V)).toPartialSelector.Fiber d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) (liftedResidualVacuum d (canonicalEdgeSegment d.graph e)) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoUnitCertificate.twoUnit_left_rawPairFiberMass_pos beta J hbeta hJ d e f hne hfirst hactiveE hactiveF hpath

/--
[twoUnit_coordinatePairContributes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoUnitCertificate.lean)
-/
@[path]
private lemma twoUnit_coordinatePairContributes_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 < beta)
  (hJ : ∀ g, 0 < J g)
  (hne : e ≠ f)
  (hfirst : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit (twoUnitFlux d.graph e f) b) ⟨d, []⟩ = some e.1)
  (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  CoordinatePairContributes (selectorSpec (V := V)).toPartialSelector beta J d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f] hactiveE (twoUnitFlux d.graph e f) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoUnitCertificate.twoUnit_coordinatePairContributes beta J hbeta hJ d e f hne hfirst hactiveE hactiveF hpath

/--
[twoUnit_rawPairFiberMass_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoUnitCertificate.lean)
-/
@[path]
private lemma twoUnit_rawPairFiberMass_eq_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (J : Sym2 V -> Real)
  (hne : e ≠ f)
  (hfirst : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit (twoUnitFlux d.graph e f) b) ⟨d, []⟩ = some e.1)
  (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  rawSourcePairFiberMass d.graph beta J (twoUnitFlux d.graph e f) ((selectorSpec (V := V)).toPartialSelector.sourceClass d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) ((selectorSpec (V := V)).toPartialSelector.Fiber d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) (liftedResidualVacuum d (canonicalEdgeSegment d.graph e)) = rawSourcePairFiberMass d.graph beta J (twoUnitFlux d.graph e f) (((selectorSpec (V := V)).toPartialSelector.sourceClass d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) ∆ stepToggleSource (selectorSpec (V := V)).toPartialSelector d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]) (shb_ActiveSegmentFiber d (canonicalEdgeSegment d.graph e) hactiveE) (liftedResidualFiber (selectorSpec (V := V)).toPartialSelector d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoUnitCertificate.twoUnit_rawPairFiberMass_eq beta J d e f hne hfirst hactiveE hactiveF hpath

/--
[canonicalBondwiseToggleExists_iff_off_twoUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoUnitCertificate.lean)
-/
@[path]
private lemma canonicalBondwiseToggleExists_iff_off_twoUnit_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (J : Sym2 V -> Real)
  (hne : e ≠ f)
  (hfirst : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit (twoUnitFlux d.graph e f) b) ⟨d, []⟩ = some e.1)
  (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  (selectorSpec (V := V)).CanonicalBondwiseToggleExists beta J d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f] hactiveE <-> ∀ m, m ≠ twoUnitFlux d.graph e f -> CoordinatePairContributes (selectorSpec (V := V)).toPartialSelector beta J d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f] hactiveE m -> ∃ path : Finset (Copy d.graph m), ∀ T, BondwisePairEvent ((program (V := V)).runSpec d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)) d.graph m T <-> BondwisePairEvent (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE) ((program (V := V)).liftedResidualRunSpec d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]) d.graph m (T ∆ path) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoUnitCertificate.canonicalBondwiseToggleExists_iff_off_twoUnit beta J d e f hne hfirst hactiveE hactiveF hpath

/--
[nonempty_canonicalCertificate_iff_off_twoUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoUnitCertificate.lean)
-/
@[path]
private lemma nonempty_canonicalCertificate_iff_off_twoUnit_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (J : Sym2 V -> Real)
  (hne : e ≠ f)
  (hfirst : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit (twoUnitFlux d.graph e f) b) ⟨d, []⟩ = some e.1)
  (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  Nonempty (AsymmetricBondwiseCoordinateCertificate ((program (V := V)).runSpec d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)) (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE) ((program (V := V)).liftedResidualRunSpec d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]) (selectorSpec (V := V)).toPartialSelector beta J d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f] hactiveE) <-> ∀ m, m ≠ twoUnitFlux d.graph e f -> CoordinatePairContributes (selectorSpec (V := V)).toPartialSelector beta J d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f] hactiveE m -> ∃ path : Finset (Copy d.graph m), ∀ T, BondwisePairEvent ((program (V := V)).runSpec d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)) d.graph m T <-> BondwisePairEvent (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE) ((program (V := V)).liftedResidualRunSpec d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]) d.graph m (T ∆ path) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoUnitCertificate.nonempty_canonicalCertificate_iff_off_twoUnit beta J d e f hne hfirst hactiveE hactiveF hpath


-- created on 2026-10-23
