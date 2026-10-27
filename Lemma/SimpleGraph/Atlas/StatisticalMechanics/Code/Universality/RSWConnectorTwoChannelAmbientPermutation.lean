import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelAmbientPermutation.Part5
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_twoChannelFullPhysicalAmbientFailureEmbedding_success](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalAmbientFailureEmbedding_success_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith)
  (rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'}) :
-- imply
  rlc_twoChannelFullPhysicalAmbientFailureEmbedding hfaith hstatic rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalAmbientFailureEmbedding_success hfaith hstatic rho

/--
[rlc_twoChannelFullPhysicalAmbientFailureEmbedding_apply_of_not_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalAmbientFailureEmbedding_apply_of_not_edge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (RlcConnectorVertex n)}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith)
  (rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'})
  (he : e ∉ (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) :
-- imply
  rlc_twoChannelFullPhysicalAmbientFailureEmbedding hfaith hstatic rho e = rho.1 e := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalAmbientFailureEmbedding_apply_of_not_edge hfaith hstatic rho e he

/--
[rlc_twoChannelFullPhysicalAmbientFailureEmbedding_agreesOff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalAmbientFailureEmbedding_agreesOff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith)
  (rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'}) :
-- imply
  FK.AgreesOff (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset rho.1 (rlc_twoChannelFullPhysicalAmbientFailureEmbedding hfaith hstatic rho) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalAmbientFailureEmbedding_agreesOff hfaith hstatic rho

/--
[rlc_connectorTwoChannelGraph_edgeFinset_disjoint_traceWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_connectorTwoChannelGraph_edgeFinset_disjoint_traceWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Disjoint (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
-- proof
  apply StatMech.Universality.rlc_connectorTwoChannelGraph_edgeFinset_disjoint_traceWiring gamma gamma'

/--
[rlc_connectorExtendConfig_pathPairOpen_of_trace_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_connectorExtendConfig_pathPairOpen_of_trace_open_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (htrace : ∀ e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true) :
-- imply
  rlc_connectorExtendConfig psi ∈ rlc_pathPairOpen (gamma, gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorExtendConfig_pathPairOpen_of_trace_open gamma gamma' psi htrace

/--
[rlc_allOpenConnectorConfig_displays_two_pathPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_allOpenConnectorConfig_displays_two_pathPairs_eq
  {n : Int}
  {pair pair' : RlcDiagonalPathPair n} :
-- imply
  let psi : ConfigSpace (Sym2 (RlcConnectorVertex n)) := fun _ ↦ true rlc_connectorExtendConfig psi ∈ rlc_pathPairOpen pair ∩ rlc_pathPairOpen pair' := by
-- proof
  apply StatMech.Universality.rlc_allOpenConnectorConfig_displays_two_pathPairs pair pair'

/--
[rlc_finiteExtremalPairCandidate_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_finiteExtremalPairCandidate_pairwiseDisjoint_eq
  {n : Int}
-- given
  (hright : RlcRightEnvelopeProperty n)
  (hleft : RlcLeftEnvelopeProperty n) :
-- imply
  Pairwise fun pair pair' : RlcDiagonalPathPair n ↦ Disjoint (rlc_finiteExtremalPairCandidate pair.1 pair.2) (rlc_finiteExtremalPairCandidate pair'.1 pair'.2) := by
-- proof
  apply StatMech.Universality.rlc_finiteExtremalPairCandidate_pairwiseDisjoint hright hleft

/--
[rlc_activeFiniteExtremalPairCandidate_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_activeFiniteExtremalPairCandidate_pairwiseDisjoint_eq
  {n : Int}
-- given
  (hright : RlcRightEnvelopeProperty n)
  (hleft : RlcLeftEnvelopeProperty n) :
-- imply
  Pairwise fun pair pair' : RlcTwoChannelActiveFiniteExtremalPair n ↦ Disjoint (rlc_finiteExtremalPairCandidate pair.1.1 pair.1.2) (rlc_finiteExtremalPairCandidate pair'.1.1 pair'.1.2) := by
-- proof
  apply StatMech.Universality.rlc_activeFiniteExtremalPairCandidate_pairwiseDisjoint hright hleft

/--
[rlc_exists_finiteExtremalPairCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_exists_finiteExtremalPairCandidate_eq
  {n : Int}
  {psi : RlcTwoChannelFiniteDiagonalConfig n} :
-- imply
  ∃ pair : RlcDiagonalPathPair n, psi.1 ∈ rlc_finiteExtremalPairCandidate pair.1 pair.2 := by
-- proof
  apply StatMech.Universality.rlc_exists_finiteExtremalPairCandidate psi

/--
[rlc_twoChannelFiniteExtremalPairSelector_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFiniteExtremalPairSelector_selected_eq
  {n : Int}
  {psi : RlcTwoChannelFiniteDiagonalConfig n} :
-- imply
  psi.1 ∈ rlc_finiteExtremalPairCandidate (rlc_twoChannelFiniteExtremalPairSelector psi).1.1 (rlc_twoChannelFiniteExtremalPairSelector psi).1.2 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFiniteExtremalPairSelector_selected psi

/--
[rlc_twoChannelFiniteExtremalPairSelector_eq_of_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFiniteExtremalPairSelector_eq_of_selected_eq
  {n : Int}
  {psi : RlcTwoChannelFiniteDiagonalConfig n}
  {pair : RlcTwoChannelActiveFiniteExtremalPair n}
-- given
  (hright : RlcRightEnvelopeProperty n)
  (hleft : RlcLeftEnvelopeProperty n)
  (hselected : psi.1 ∈ rlc_finiteExtremalPairCandidate pair.1.1 pair.1.2) :
-- imply
  rlc_twoChannelFiniteExtremalPairSelector psi = pair := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFiniteExtremalPairSelector_eq_of_selected hright hleft psi pair hselected

/--
[rlc_twoChannelIndexedAmbientFailureMap_success](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedAmbientFailureMap_success_eq
  {n : Int}
  {pair : I → RlcDiagonalPathPair n}
  {x : RlcTwoChannelIndexedSelectedFailure I pair}
-- given
  (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
  (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection (pair i).1 (pair i).2 (hfaith i)) :
-- imply
  rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x ∈ rlc_finiteTwoChannelConnectorEvent (pair x.index).1 (pair x.index).2 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedAmbientFailureMap_success pair hfaith hstatic x

/--
[rlc_twoChannelIndexedAmbientFailureMap_agreesOff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedAmbientFailureMap_agreesOff_eq
  {n : Int}
  {pair : I → RlcDiagonalPathPair n}
  {x : RlcTwoChannelIndexedSelectedFailure I pair}
-- given
  (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
  (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection (pair i).1 (pair i).2 (hfaith i)) :
-- imply
  FK.AgreesOff (rlc_connectorTwoChannelGraph (pair x.index).1 (pair x.index).2).edgeFinset x.config (rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedAmbientFailureMap_agreesOff pair hfaith hstatic x

/--
[rlc_twoChannelIndexedAmbientFailureMap_collision_agreesOff_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedAmbientFailureMap_collision_agreesOff_union_eq
  {n : Int}
  {pair : I → RlcDiagonalPathPair n}
  {x y : RlcTwoChannelIndexedSelectedFailure I pair}
-- given
  (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
  (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection (pair i).1 (pair i).2 (hfaith i))
  (hxy : rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x = rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic y) :
-- imply
  ∀ e, e ∉ (rlc_connectorTwoChannelGraph (pair x.index).1 (pair x.index).2).edgeFinset → e ∉ (rlc_connectorTwoChannelGraph (pair y.index).1 (pair y.index).2).edgeFinset → x.config e = y.config e := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedAmbientFailureMap_collision_agreesOff_union pair hfaith hstatic hxy

/--
[rlc_twoChannelIndexedAmbientFailureMap_trace_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedAmbientFailureMap_trace_open_eq
  {n : Int}
  {pair : I → RlcDiagonalPathPair n}
  {x : RlcTwoChannelIndexedSelectedFailure I pair}
-- given
  (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
  (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection (pair i).1 (pair i).2 (hfaith i)) :
-- imply
  ∀ e ∈ (rlc_connectorTraceWiring (pair x.index).1 (pair x.index).2).edgeFinset, rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x e = true := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedAmbientFailureMap_trace_open pair hfaith hstatic x

/--
[rlc_twoChannelActiveAmbientTargetSelector_eq_iff_stable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelActiveAmbientTargetSelector_eq_iff_stable_eq
  {n : Int}
  {x : RlcTwoChannelIndexedSelectedFailure (RlcTwoChannelActiveFiniteExtremalPair n) Subtype.val}
-- given
  (hright : RlcRightEnvelopeProperty n)
  (hleft : RlcLeftEnvelopeProperty n)
  (hfaith : ∀ i : RlcTwoChannelActiveFiniteExtremalPair n, RlcBookFaithfulTracePair i.1.1 i.1.2)
  (hstatic : ∀ i : RlcTwoChannelActiveFiniteExtremalPair n, RlcTwoChannelFullPhysicalStaticCutIntersection i.1.1 i.1.2 (hfaith i)) :
-- imply
  rlc_twoChannelIndexedAmbientTargetSelector Subtype.val hfaith hstatic x = x.index ↔ rlc_twoChannelIndexedAmbientFailureMap Subtype.val hfaith hstatic x ∈ rlc_finiteExtremalPairCandidate x.index.1.1 x.index.1.2 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelActiveAmbientTargetSelector_eq_iff_stable hright hleft hfaith hstatic x

/--
[rlc_twoChannelIndexedAmbientFailureMap_glues_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedAmbientFailureMap_glues_horizontal_eq
  {n : Int}
  {pair : I → RlcDiagonalPathPair n}
  {x : RlcTwoChannelIndexedSelectedFailure I pair}
-- given
  (hn : 0 < n)
  (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
  (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection (pair i).1 (pair i).2 (hfaith i)) :
-- imply
  rlc_connectorExtendConfig (rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x) ∈ horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedAmbientFailureMap_glues_horizontal hn pair hfaith hstatic x

/--
[rlc_twoChannelIndexedAmbientCollisionRecovery_of_target_stable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedAmbientCollisionRecovery_of_target_stable_eq
  {n : Int}
  {pair : I → RlcDiagonalPathPair n}
-- given
  (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
  (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection (pair i).1 (pair i).2 (hfaith i))
  (hdisjoint : Pairwise fun i j : I ↦ Disjoint (rlc_finiteExtremalPairCandidate (pair i).1 (pair i).2) (rlc_finiteExtremalPairCandidate (pair j).1 (pair j).2))
  (hstable : ∀ x : RlcTwoChannelIndexedSelectedFailure I pair, rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x ∈ rlc_finiteExtremalPairCandidate (pair x.index).1 (pair x.index).2) :
-- imply
  RlcTwoChannelIndexedAmbientCollisionRecovery pair hfaith hstatic := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedAmbientCollisionRecovery_of_target_stable pair hfaith hstatic hdisjoint hstable

/--
[rlc_twoChannelActiveAmbientCollisionRecovery_of_target_stable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelActiveAmbientCollisionRecovery_of_target_stable_eq
  {n : Int}
-- given
  (hright : RlcRightEnvelopeProperty n)
  (hleft : RlcLeftEnvelopeProperty n)
  (hfaith : ∀ i : RlcTwoChannelActiveFiniteExtremalPair n, RlcBookFaithfulTracePair i.1.1 i.1.2)
  (hstatic : ∀ i : RlcTwoChannelActiveFiniteExtremalPair n, RlcTwoChannelFullPhysicalStaticCutIntersection i.1.1 i.1.2 (hfaith i))
  (hstable : ∀ x : RlcTwoChannelIndexedSelectedFailure (RlcTwoChannelActiveFiniteExtremalPair n) Subtype.val, rlc_twoChannelIndexedAmbientFailureMap Subtype.val hfaith hstatic x ∈ rlc_finiteExtremalPairCandidate x.index.1.1 x.index.1.2) :
-- imply
  RlcTwoChannelIndexedAmbientCollisionRecovery Subtype.val hfaith hstatic := by
-- proof
  apply StatMech.Universality.rlc_twoChannelActiveAmbientCollisionRecovery_of_target_stable hright hleft hfaith hstatic hstable

/--
[rlc_twoChannelIndexedAmbientCollisionRecovery_const_bool_no_go](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelAmbientPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelIndexedAmbientCollisionRecovery_const_bool_no_go_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith)
  (hselected : rho ∈ rlc_finiteExtremalPairCandidate gamma gamma')
  (hfailure : rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  ¬ RlcTwoChannelIndexedAmbientCollisionRecovery (I := Bool) (fun _ ↦ (gamma, gamma')) (fun _ ↦ hfaith) (fun _ ↦ hstatic) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelIndexedAmbientCollisionRecovery_const_bool_no_go hfaith hstatic rho hselected hfailure


-- created on 2026-10-23
