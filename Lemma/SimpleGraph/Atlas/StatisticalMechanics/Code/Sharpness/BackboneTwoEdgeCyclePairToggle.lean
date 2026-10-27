import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCyclePairToggle
open SimpleGraph Finset BigOperators StatMech StatMech.Sharpness StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle


/--
[completeEvent_congr_bits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma completeEvent_congr_bits_eq
  {P : BondwiseSegmentProgram (Fin 6)}
  {d : shb_ExplorationDomain (Fin 6)}
  {word : List (shb_ExplorationSegment (Fin 6))}
  {p q : d.graph.edgeFinset → Nat}
-- given
  (hbits : fluxBitConfig d.graph P.bit p = fluxBitConfig d.graph P.bit q) :
-- imply
  P.CompleteEvent d word p ↔ P.CompleteEvent d word q := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.completeEvent_congr_bits P d word p q hbits

/--
[activeSegmentFiber_congr_bits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma activeSegmentFiber_congr_bits_eq
  {d : shb_ExplorationDomain (Fin 6)}
  {e : d.graph.edgeFinset}
  {p q : d.graph.edgeFinset → Nat}
-- given
  (he : canonicalEdgeSegment d.graph e ∈ d.active)
  (hbits : fluxBitConfig d.graph oddBit p = fluxBitConfig d.graph oddBit q) :
-- imply
  shb_ActiveSegmentFiber d (canonicalEdgeSegment d.graph e) he p ↔ shb_ActiveSegmentFiber d (canonicalEdgeSegment d.graph e) he q := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.activeSegmentFiber_congr_bits d e he p q hbits

/--
[complete_pair_bits_eq_twoUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma complete_pair_bits_eq_twoUnit_eq
  {p : domain.graph.edgeFinset → Nat}
-- given
  (hcomplete : (BackboneTwoEdgeExhaustiveProgram.program (V := Fin 6)).CompleteEvent domain [canonicalEdgeSegment domain.graph headEdge, canonicalEdgeSegment domain.graph suffixEdge] p) :
-- imply
  fluxBitConfig domain.graph oddBit p = fluxBitConfig domain.graph oddBit (twoUnitFlux domain.graph headEdge suffixEdge) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.complete_pair_bits_eq_twoUnit p hcomplete

/--
[fluxBitConfig_oddBit_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma fluxBitConfig_oddBit_eq_iff_eq
  {p q : domain.graph.edgeFinset → Nat} :
-- imply
  fluxBitConfig domain.graph oddBit p = fluxBitConfig domain.graph oddBit q ↔ ∀ e, Odd (p e) ↔ Odd (q e) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.fluxBitConfig_oddBit_eq_iff p q

/--
[fluxBitConfig_oddBit_eq_iff_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma fluxBitConfig_oddBit_eq_iff_on_eq
  {G : SimpleGraph (Fin 6)}
  [DecidableRel G.Adj]
  {p q : G.edgeFinset → Nat} :
-- imply
  fluxBitConfig G oddBit p = fluxBitConfig G oddBit q ↔ ∀ e, Odd (p e) ↔ Odd (q e) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.fluxBitConfig_oddBit_eq_iff_on p q

/--
[filter_symmDiff_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma filter_symmDiff_edge_eq
  {S U : Finset (Copy domain.graph superposition)}
  {g : domain.graph.edgeFinset} :
-- imply
  (S ∆ U).filter (fun i : Copy domain.graph superposition => i.1 = g) = S.filter (fun i : Copy domain.graph superposition => i.1 = g) ∆ U.filter (fun i : Copy domain.graph superposition => i.1 = g) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.filter_symmDiff_edge S U g

/--
[profile_toggle_suffix_odd_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma profile_toggle_suffix_odd_iff_eq
  {T : Finset (Copy domain.graph superposition)}
  {g : domain.graph.edgeFinset} :
-- imply
  Odd (profileFlux domain.graph superposition (T ∆ {suffixCopy}) g) ↔ if g = suffixEdge then ¬ Odd (profileFlux domain.graph superposition T g) else Odd (profileFlux domain.graph superposition T g) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.profile_toggle_suffix_odd_iff T g

/--
[profile_compl_odd_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma profile_compl_odd_iff_eq
  {T : Finset (Copy domain.graph superposition)}
  {g : domain.graph.edgeFinset} :
-- imply
  Odd (profileFlux domain.graph superposition (univ \ T) g) ↔ if g = headEdge ∨ g = suffixEdge then ¬ Odd (profileFlux domain.graph superposition T g) else Odd (profileFlux domain.graph superposition T g) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.profile_compl_odd_iff T g

/--
[profile_toggle_suffix_bits_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma profile_toggle_suffix_bits_iff_eq
  {T : Finset (Copy domain.graph superposition)} :
-- imply
  fluxBitConfig domain.graph oddBit (profileFlux domain.graph superposition (T ∆ {suffixCopy})) = fluxBitConfig domain.graph oddBit (unitFlux domain.graph headEdge) ↔ fluxBitConfig domain.graph oddBit (profileFlux domain.graph superposition T) = fluxBitConfig domain.graph oddBit (twoUnitFlux domain.graph headEdge suffixEdge) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.profile_toggle_suffix_bits_iff T

/--
[profile_compl_bits_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma profile_compl_bits_iff_eq
  {T : Finset (Copy domain.graph superposition)} :
-- imply
  fluxBitConfig domain.graph oddBit (profileFlux domain.graph superposition (univ \ T)) = fluxBitConfig domain.graph oddBit (unitFlux domain.graph suffixEdge) ↔ fluxBitConfig domain.graph oddBit (profileFlux domain.graph superposition T) = fluxBitConfig domain.graph oddBit (unitFlux domain.graph headEdge) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.profile_compl_bits_iff T

/--
[profile_compl_zero_bits_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma profile_compl_zero_bits_iff_eq
  {T : Finset (Copy domain.graph superposition)} :
-- imply
  fluxBitConfig domain.graph oddBit (profileFlux domain.graph superposition (univ \ T)) = fluxBitConfig domain.graph oddBit 0 ↔ fluxBitConfig domain.graph oddBit (profileFlux domain.graph superposition T) = fluxBitConfig domain.graph oddBit (twoUnitFlux domain.graph headEdge suffixEdge) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.profile_compl_zero_bits_iff T

/--
[restrictResidual_bits_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma restrictResidual_bits_eq_eq
  {p q : domain.graph.edgeFinset → Nat}
-- given
  (hbits : fluxBitConfig domain.graph oddBit p = fluxBitConfig domain.graph oddBit q) :
-- imply
  fluxBitConfig residualGraph oddBit (restrictResidual p) = fluxBitConfig residualGraph oddBit (restrictResidual q) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.restrictResidual_bits_eq p q hbits

/--
[restrictResidual_unitSuffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma restrictResidual_unitSuffix_eq :
-- imply
  restrictResidual (unitFlux domain.graph suffixEdge) = unitFlux residualGraph residualSuffix := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.restrictResidual_unitSuffix

/--
[profile_head_eq_zero_of_unitSuffix_bits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma profile_head_eq_zero_of_unitSuffix_bits_eq
  {T : Finset (Copy domain.graph superposition)}
-- given
  (hbits : fluxBitConfig domain.graph oddBit (profileFlux domain.graph superposition T) = fluxBitConfig domain.graph oddBit (unitFlux domain.graph suffixEdge)) :
-- imply
  profileFlux domain.graph superposition T headEdge = 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.profile_head_eq_zero_of_unitSuffix_bits T hbits

/--
[exhaustive_suffix_of_unitSuffix_bits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma exhaustive_suffix_of_unitSuffix_bits_eq
  {T : Finset (Copy domain.graph superposition)}
-- given
  (hbits : fluxBitConfig domain.graph oddBit (profileFlux domain.graph superposition T) = fluxBitConfig domain.graph oddBit (unitFlux domain.graph suffixEdge)) :
-- imply
  ((BackboneTwoEdgeExhaustiveProgram.program (V := Fin 6)).liftedResidualRunSpec domain (canonicalEdgeSegment domain.graph headEdge) [canonicalEdgeSegment domain.graph suffixEdge]).Event domain.graph (profileFlux domain.graph superposition T) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.exhaustive_suffix_of_unitSuffix_bits T hbits

/--
[base_singleton_complete_bits_eq_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma base_singleton_complete_bits_eq_unit_eq
  {d : shb_ExplorationDomain (Fin 6)}
  {e : d.graph.edgeFinset}
  {p : d.graph.edgeFinset → Nat}
-- given
  (hcomplete : (BackboneTwoEdgeBondProgram.program (V := Fin 6)).CompleteEvent d [canonicalEdgeSegment d.graph e] p) :
-- imply
  fluxBitConfig d.graph oddBit p = fluxBitConfig d.graph oddBit (unitFlux d.graph e) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.base_singleton_complete_bits_eq_unit d e p hcomplete

/--
[extendFlux_bits_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma extendFlux_bits_eq_eq
  {r q : residualGraph.edgeFinset → Nat}
-- given
  (hbits : fluxBitConfig residualGraph oddBit r = fluxBitConfig residualGraph oddBit q) :
-- imply
  fluxBitConfig domain.graph oddBit (extendFlux residualLe r) = fluxBitConfig domain.graph oddBit (extendFlux residualLe q) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.extendFlux_bits_eq r q hbits

/--
[unitSuffix_bits_of_exhaustive_suffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma unitSuffix_bits_of_exhaustive_suffix_eq
  {T : Finset (Copy domain.graph superposition)}
-- given
  (hsuffix : ((BackboneTwoEdgeExhaustiveProgram.program (V := Fin 6)).liftedResidualRunSpec domain (canonicalEdgeSegment domain.graph headEdge) [canonicalEdgeSegment domain.graph suffixEdge]).Event domain.graph (profileFlux domain.graph superposition T)) :
-- imply
  fluxBitConfig domain.graph oddBit (profileFlux domain.graph superposition T) = fluxBitConfig domain.graph oddBit (unitFlux domain.graph suffixEdge) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.unitSuffix_bits_of_exhaustive_suffix T hsuffix

/--
[activeHead_of_unitHead_bits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma activeHead_of_unitHead_bits_eq
  {T : Finset (Copy domain.graph superposition)}
-- given
  (hbits : fluxBitConfig domain.graph oddBit (profileFlux domain.graph superposition T) = fluxBitConfig domain.graph oddBit (unitFlux domain.graph headEdge)) :
-- imply
  (activeSegmentRunSpec domain (canonicalEdgeSegment domain.graph headEdge) head_active).Event domain.graph (profileFlux domain.graph superposition T) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.activeHead_of_unitHead_bits T hbits

/--
[exhaustive_full_of_twoUnit_bits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma exhaustive_full_of_twoUnit_bits_eq
  {T : Finset (Copy domain.graph superposition)}
-- given
  (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible (fun _ b => fluxBitConfig domain.graph oddBit (twoUnitFlux domain.graph headEdge suffixEdge) b) ⟨domain, []⟩ = some headEdge.1)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment domain.graph headEdge) (canonicalEdgeSegment domain.graph suffixEdge))
  (hbits : fluxBitConfig domain.graph oddBit (profileFlux domain.graph superposition T) = fluxBitConfig domain.graph oddBit (twoUnitFlux domain.graph headEdge suffixEdge)) :
-- imply
  ((BackboneTwoEdgeExhaustiveProgram.program (V := Fin 6)).runSpec domain [canonicalEdgeSegment domain.graph headEdge, canonicalEdgeSegment domain.graph suffixEdge]).Event domain.graph (profileFlux domain.graph superposition T) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.exhaustive_full_of_twoUnit_bits T hfirst hpath hbits

/--
[profile_head_eq_zero_of_zero_bits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma profile_head_eq_zero_of_zero_bits_eq
  {T : Finset (Copy domain.graph superposition)}
-- given
  (hbits : fluxBitConfig domain.graph oddBit (profileFlux domain.graph superposition T) = fluxBitConfig domain.graph oddBit 0) :
-- imply
  profileFlux domain.graph superposition T headEdge = 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.profile_head_eq_zero_of_zero_bits T hbits

/--
[residualVacuum_of_zero_bits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma residualVacuum_of_zero_bits_eq
  {T : Finset (Copy domain.graph superposition)}
-- given
  (hbits : fluxBitConfig domain.graph oddBit (profileFlux domain.graph superposition T) = fluxBitConfig domain.graph oddBit 0) :
-- imply
  (residualVacuumRunSpec domain (canonicalEdgeSegment domain.graph headEdge)).Event domain.graph (profileFlux domain.graph superposition T) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.residualVacuum_of_zero_bits T hbits

/--
[exhaustive_cycle_pair_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma exhaustive_cycle_pair_toggle_eq
  {T : Finset (Copy domain.graph superposition)}
-- given
  (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible (fun _ b => fluxBitConfig domain.graph oddBit (twoUnitFlux domain.graph headEdge suffixEdge) b) ⟨domain, []⟩ = some headEdge.1)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment domain.graph headEdge) (canonicalEdgeSegment domain.graph suffixEdge)) :
-- imply
  BondwisePairEvent ((BackboneTwoEdgeExhaustiveProgram.program (V := Fin 6)).runSpec domain [canonicalEdgeSegment domain.graph headEdge, canonicalEdgeSegment domain.graph suffixEdge]) (residualVacuumRunSpec domain (canonicalEdgeSegment domain.graph headEdge)) domain.graph superposition T ↔ BondwisePairEvent (activeSegmentRunSpec domain (canonicalEdgeSegment domain.graph headEdge) head_active) ((BackboneTwoEdgeExhaustiveProgram.program (V := Fin 6)).liftedResidualRunSpec domain (canonicalEdgeSegment domain.graph headEdge) [canonicalEdgeSegment domain.graph suffixEdge]) domain.graph superposition (T ∆ {suffixCopy}) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.exhaustive_cycle_pair_toggle hfirst hpath T

/--
[exhaustive_cycle_pair_toggle_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean)
-/
@[path]
private lemma exhaustive_cycle_pair_toggle_exists_eq
-- given
  (hfirst : BackboneTwoEdgeBondProgram.scan.firstAdmissible (fun _ b => fluxBitConfig domain.graph oddBit (twoUnitFlux domain.graph headEdge suffixEdge) b) ⟨domain, []⟩ = some headEdge.1)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment domain.graph headEdge) (canonicalEdgeSegment domain.graph suffixEdge)) :
-- imply
  ∃ path : Finset (Copy domain.graph superposition), ∀ T, BondwisePairEvent ((BackboneTwoEdgeExhaustiveProgram.program (V := Fin 6)).runSpec domain [canonicalEdgeSegment domain.graph headEdge, canonicalEdgeSegment domain.graph suffixEdge]) (residualVacuumRunSpec domain (canonicalEdgeSegment domain.graph headEdge)) domain.graph superposition T ↔ BondwisePairEvent (activeSegmentRunSpec domain (canonicalEdgeSegment domain.graph headEdge) head_active) ((BackboneTwoEdgeExhaustiveProgram.program (V := Fin 6)).liftedResidualRunSpec domain (canonicalEdgeSegment domain.graph headEdge) [canonicalEdgeSegment domain.graph suffixEdge]) domain.graph superposition (T ∆ path) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle.exhaustive_cycle_pair_toggle_exists hfirst hpath


-- created on 2026-10-23
