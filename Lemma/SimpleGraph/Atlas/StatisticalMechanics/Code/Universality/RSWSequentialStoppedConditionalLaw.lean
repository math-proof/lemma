import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_connectorForcedTraceActiveWeight_eq_separate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorForcedTraceActiveWeight_eq_separate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet} :
-- imply
  rlc_connectorForcedTraceActiveWeight gamma gamma' p q eta = p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card * FK.activeBCWeight (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (fun _ => p) q eta := by
-- proof
  apply StatMech.Universality.rlc_connectorForcedTraceActiveWeight_eq_separate gamma gamma' p q eta

/--
[rlc_connectorForcedTraceActiveZ_eq_separate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorForcedTraceActiveZ_eq_separate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real} :
-- imply
  rlc_connectorForcedTraceActiveZ gamma gamma' p q = p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card * FK.activeBCZ (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (fun _ => p) q := by
-- proof
  apply StatMech.Universality.rlc_connectorForcedTraceActiveZ_eq_separate gamma gamma' p q

/--
[rlc_connectorForcedTraceActiveProb_eq_separate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorForcedTraceActiveProb_eq_separate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet}
-- given
  (hp : 0 < p) :
-- imply
  rlc_connectorForcedTraceActiveProb gamma gamma' p q eta = FK.activeBCProb (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (fun _ => p) q eta := by
-- proof
  apply StatMech.Universality.rlc_connectorForcedTraceActiveProb_eq_separate gamma gamma' hp eta

/--
[rlc_connectorForcedTraceActiveEventMass_eq_activeSeparate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorForcedTraceActiveEventMass_eq_activeSeparate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p) :
-- imply
  rlc_connectorForcedTraceActiveEventMass gamma gamma' p q = FK.activeBCProbOf (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (fun _ => p) q (rlc_connectorActiveEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorForcedTraceActiveEventMass_eq_activeSeparate gamma gamma' hp

/--
[rlc_connectorActiveEvent_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorActiveEvent_preimage_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') ⁻¹' rlc_connectorActiveEvent gamma gamma' = rlc_finiteConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorActiveEvent_preimage gamma gamma'

/--
[rlc_connectorForcedTraceActiveEventMass_eq_separate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorForcedTraceActiveEventMass_eq_separate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  rlc_connectorForcedTraceActiveEventMass gamma gamma' p q = FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorForcedTraceActiveEventMass_eq_separate gamma gamma' hp hp1 hq

/--
[rlc_connectorTraceFibreConfig_agreesOff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorTraceFibreConfig_agreesOff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet} :
-- imply
  FK.AgreesOff (rlc_connectorTraceFibreInside gamma gamma') (rlc_connectorTraceFibreReference gamma gamma') (rlc_connectorTraceFibreConfig gamma gamma' eta) := by
-- proof
  apply StatMech.Universality.rlc_connectorTraceFibreConfig_agreesOff gamma gamma' eta

/--
[rlc_connectorTraceFibreConfig_restrictActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorTraceFibreConfig_restrictActive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet} :
-- imply
  FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorTraceFibreConfig gamma gamma' eta) = eta := by
-- proof
  apply StatMech.Universality.rlc_connectorTraceFibreConfig_restrictActive gamma gamma' eta

/--
[rlc_connectorTraceFibreConfig_restrictActive_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorTraceFibreConfig_restrictActive_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hrho : FK.AgreesOff (rlc_connectorTraceFibreInside gamma gamma') (rlc_connectorTraceFibreReference gamma gamma') rho) :
-- imply
  rlc_connectorTraceFibreConfig gamma gamma' (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') rho) = rho := by
-- proof
  apply StatMech.Universality.rlc_connectorTraceFibreConfig_restrictActive_eq gamma gamma' hrho

/--
[rlc_connectorTraceFibre_bcWeight_bot_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorTraceFibre_bcWeight_bot_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet} :
-- imply
  FK.bcWeight (rlc_connectorAugmentedPlanarDomain gamma gamma').G (⊥ : SimpleGraph (RlcConnectorVertex n)) p q (rlc_connectorTraceFibreConfig gamma gamma' eta) = rlc_connectorForcedTraceActiveWeight gamma gamma' p q eta := by
-- proof
  apply StatMech.Universality.rlc_connectorTraceFibre_bcWeight_bot_eq gamma gamma' p q eta

/--
[rlc_connectorTraceFibre_inducedBcZ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorTraceFibre_inducedBcZ_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real} :
-- imply
  FK.inducedBcZ (rlc_connectorAugmentedPlanarDomain gamma gamma').G (⊥ : SimpleGraph (RlcConnectorVertex n)) p q (rlc_connectorTraceFibreInside gamma gamma') (rlc_connectorTraceFibreReference gamma gamma') = rlc_connectorForcedTraceActiveZ gamma gamma' p q := by
-- proof
  apply StatMech.Universality.rlc_connectorTraceFibre_inducedBcZ_eq gamma gamma' p q

/--
[rlc_connectorTraceFibre_condBcProb_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorTraceFibre_condBcProb_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
  {eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet} :
-- imply
  FK.condBcProb (rlc_connectorAugmentedPlanarDomain gamma gamma').G (⊥ : SimpleGraph (RlcConnectorVertex n)) p q (rlc_connectorTraceFibreInside gamma gamma') (rlc_connectorTraceFibreReference gamma gamma') (rlc_connectorTraceFibreConfig gamma gamma' eta) = rlc_connectorForcedTraceActiveProb gamma gamma' p q eta := by
-- proof
  apply StatMech.Universality.rlc_connectorTraceFibre_condBcProb_eq gamma gamma' p q eta

/--
[rlc_connectorTraceFibreCondEventMass_eq_forcedTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorTraceFibreCondEventMass_eq_forcedTrace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real} :
-- imply
  rlc_connectorTraceFibreCondEventMass gamma gamma' p q = rlc_connectorForcedTraceActiveEventMass gamma gamma' p q := by
-- proof
  apply StatMech.Universality.rlc_connectorTraceFibreCondEventMass_eq_forcedTrace gamma gamma' p q

/--
[rlc_connectorTraceFibreCondEventMass_eq_separate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorTraceFibreCondEventMass_eq_separate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  rlc_connectorTraceFibreCondEventMass gamma gamma' p q = FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') p q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorTraceFibreCondEventMass_eq_separate gamma gamma' hp hp1 hq

/--
[rlc_connectorTraceFibreCondEventMass_selfDual_ge_one_div_one_add_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorTraceFibreCondEventMass_selfDual_ge_one_div_one_add_q_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
-- given
  (hq : 1 <= q)
  (hdual : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')ᶜ <= FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  1 / (1 + q) <= rlc_connectorTraceFibreCondEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q := by
-- proof
  apply StatMech.Universality.rlc_connectorTraceFibreCondEventMass_selfDual_ge_one_div_one_add_q gamma gamma' hq hdual

/--
[rlc_connectorExtendConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorExtendConfig_apply_eq
  {n : Int}
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {e : Sym2 (RlcConnectorVertex n)} :
-- imply
  rlc_connectorExtendConfig psi (e.map Subtype.val) = psi e := by
-- proof
  apply StatMech.Universality.rlc_connectorExtendConfig_apply psi e

/--
[rlc_extremalPairCandidateEdge_exists_connectorLift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_extremalPairCandidateEdge_exists_connectorLift_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ rlc_extremalPairCandidateEdges (gamma, gamma')) :
-- imply
  ∃ f : Sym2 (RlcConnectorVertex n), f.map Subtype.val = e := by
-- proof
  apply StatMech.Universality.rlc_extremalPairCandidateEdge_exists_connectorLift gamma gamma' he

/--
[rlc_finiteExtremalPairCandidate_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_finiteExtremalPairCandidate_dependsOn_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  _root_.DependsOn ((rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real))) (rlc_finiteExtremalPairCandidateEdges gamma gamma' : Set (Sym2 (RlcConnectorVertex n))) := by
-- proof
  apply StatMech.Universality.rlc_finiteExtremalPairCandidate_dependsOn gamma gamma'

/--
[rlc_connectorRestrictConfig_mem_finiteExtremalPairCandidate_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorRestrictConfig_mem_finiteExtremalPairCandidate_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  rlc_connectorRestrictConfig omega ∈ rlc_finiteExtremalPairCandidate gamma gamma' ↔ omega ∈ rlc_extremalPairCandidate (gamma, gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorRestrictConfig_mem_finiteExtremalPairCandidate_iff gamma gamma' omega

/--
[rlc_finiteExtremalPairCandidate_dependsOnOutside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_finiteExtremalPairCandidate_dependsOnOutside_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hdisj : Disjoint (rlc_finiteExtremalPairCandidateEdges gamma gamma') (rlc_connectorFiniteGraph gamma gamma').edgeFinset) :
-- imply
  FK.DependsOnOutside (rlc_connectorFiniteGraph gamma gamma').edgeFinset (rlc_finiteExtremalPairCandidate gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteExtremalPairCandidate_dependsOnOutside gamma gamma' hdisj

/--
[rlc_finiteExtremalPairCandidateEdges_disjoint_connector_of_ambient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_finiteExtremalPairCandidateEdges_disjoint_connector_of_ambient_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hdisj : Disjoint (rlc_extremalPairCandidateEdges (gamma, gamma')) (rlc_connectorEdges gamma gamma')) :
-- imply
  Disjoint (rlc_finiteExtremalPairCandidateEdges gamma gamma') (rlc_connectorFiniteGraph gamma gamma').edgeFinset := by
-- proof
  apply StatMech.Universality.rlc_finiteExtremalPairCandidateEdges_disjoint_connector_of_ambient gamma gamma' hdisj

/--
[rlc_finiteExtremalPairCandidate_trace_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_finiteExtremalPairCandidate_trace_open_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hpsi : psi ∈ rlc_finiteExtremalPairCandidate gamma gamma') :
-- imply
  ∀ e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset, psi e = true := by
-- proof
  apply StatMech.Universality.rlc_finiteExtremalPairCandidate_trace_open gamma gamma' hpsi

/--
[RlcBookFaithfulTracePair.origin_mem_strictTopSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma origin_mem_strictTopSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  origin 2 ∈ rlc_strictTopSet gamma := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.origin_mem_strictTopSet hfaith

/--
[RlcBookFaithfulTracePair.origin_mem_strictBottomSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma origin_mem_strictBottomSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  origin 2 ∈ rlc_strictBottomSet gamma' := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.origin_mem_strictBottomSet hfaith

/--
[rlc_connectorFoldRight_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorFoldRight_adj_eq
  {x y : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y) :
-- imply
  (hypercubicLattice 2).Adj (rlc_connectorFoldRight x) (rlc_connectorFoldRight y) := by
-- proof
  apply StatMech.Universality.rlc_connectorFoldRight_adj hxy

/--
[rlc_connectorFoldLeft_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorFoldLeft_adj_eq
  {x y : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y) :
-- imply
  (hypercubicLattice 2).Adj (rlc_connectorFoldLeft x) (rlc_connectorFoldLeft y) := by
-- proof
  apply StatMech.Universality.rlc_connectorFoldLeft_adj hxy

/--
[rlc_connectorFoldRight_mem_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorFoldRight_mem_rect_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_connectorAllowed gamma gamma') :
-- imply
  rlc_connectorFoldRight z ∈ rect 0 (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_connectorFoldRight_mem_rect gamma gamma' hz

/--
[rlc_connectorFoldLeft_mem_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorFoldLeft_mem_rect_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_connectorAllowed gamma gamma') :
-- imply
  rlc_connectorFoldLeft z ∈ rect (-2 * n) 0 (-n) n := by
-- proof
  apply StatMech.Universality.rlc_connectorFoldLeft_mem_rect gamma gamma' hz

/--
[rlc_connectorFoldRight_not_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorFoldRight_not_path_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_connectorAllowed gamma gamma') :
-- imply
  rlc_connectorFoldRight z ∉ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_connectorFoldRight_not_path gamma gamma' hz

/--
[rlc_connectorFoldLeft_not_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorFoldLeft_not_path_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_connectorAllowed gamma gamma') :
-- imply
  rlc_connectorFoldLeft z ∉ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_connectorFoldLeft_not_path gamma gamma' hz

/--
[RlcBookFaithfulTracePair.connectorOriginRegion_mem_strictTopSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma connectorOriginRegion_mem_strictTopSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hz : z ∈ rlc_connectorOriginRegion gamma gamma')
  (hz0 : 0 ≤ z 0) :
-- imply
  z ∈ rlc_strictTopSet gamma := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.connectorOriginRegion_mem_strictTopSet hfaith hz hz0

/--
[RlcBookFaithfulTracePair.connectorOriginRegion_mem_strictBottomSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma connectorOriginRegion_mem_strictBottomSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hz : z ∈ rlc_connectorOriginRegion gamma gamma')
  (hz0 : z 0 ≤ 0) :
-- imply
  z ∈ rlc_strictBottomSet gamma' := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.connectorOriginRegion_mem_strictBottomSet hfaith hz hz0

/--
[RlcBookFaithfulTracePair.extremalPairCandidateEdges_disjoint_connectorEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma extremalPairCandidateEdges_disjoint_connectorEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  Disjoint (rlc_extremalPairCandidateEdges (gamma, gamma')) (rlc_connectorEdges gamma gamma') := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.extremalPairCandidateEdges_disjoint_connectorEdges hfaith

/--
[rlc_rightExploredVertices_subset_of_pathVertices_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_rightExploredVertices_subset_of_pathVertices_subset_eq
  {n : Int}
  {gamma delta : RlcRightDiagonalPath n}
-- given
  (hverts : rlc_pathVertices delta.1 ⊆ rlc_pathVertices gamma.1) :
-- imply
  rlc_rightExploredVertices delta ⊆ rlc_rightExploredVertices gamma := by
-- proof
  apply StatMech.Universality.rlc_rightExploredVertices_subset_of_pathVertices_subset hverts

/--
[rlc_leftExploredVertices_subset_of_pathVertices_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_leftExploredVertices_subset_of_pathVertices_subset_eq
  {n : Int}
  {gamma delta : RlcLeftDiagonalPath n}
-- given
  (hverts : rlc_pathVertices delta.1 ⊆ rlc_pathVertices gamma.1) :
-- imply
  rlc_leftExploredVertices delta ⊆ rlc_leftExploredVertices gamma := by
-- proof
  apply StatMech.Universality.rlc_leftExploredVertices_subset_of_pathVertices_subset hverts

/--
[rlc_rightLowestCandidate_explored_eq_of_open_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_rightLowestCandidate_explored_eq_of_open_subset_eq
  {n : Int}
  {gamma delta : RlcRightDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hgamma : omega ∈ rlc_rightLowestCandidate gamma)
  (hdelta : omega ∈ rlc_pathOpen delta.1)
  (hsub : rlc_rightExploredVertices delta ⊆ rlc_rightExploredVertices gamma) :
-- imply
  rlc_rightExploredVertices delta = rlc_rightExploredVertices gamma := by
-- proof
  apply StatMech.Universality.rlc_rightLowestCandidate_explored_eq_of_open_subset hgamma hdelta hsub

/--
[rlc_leftHighestCandidate_explored_eq_of_open_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_leftHighestCandidate_explored_eq_of_open_subset_eq
  {n : Int}
  {gamma delta : RlcLeftDiagonalPath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hgamma : omega ∈ rlc_leftHighestCandidate gamma)
  (hdelta : omega ∈ rlc_pathOpen delta.1)
  (hsub : rlc_leftExploredVertices delta ⊆ rlc_leftExploredVertices gamma) :
-- imply
  rlc_leftExploredVertices delta = rlc_leftExploredVertices gamma := by
-- proof
  apply StatMech.Universality.rlc_leftHighestCandidate_explored_eq_of_open_subset hgamma hdelta hsub

/--
[RlcBookFaithfulStratumReplacement.of_subpaths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma of_subpaths_eq
  {n : Int}
  {gamma delta : RlcRightDiagonalPath n}
  {gamma' delta' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair delta delta')
  (hrEdges : rlc_pathEdges delta.1 ⊆ rlc_pathEdges gamma.1)
  (hlEdges : rlc_pathEdges delta'.1 ⊆ rlc_pathEdges gamma'.1)
  (hrVerts : rlc_pathVertices delta.1 ⊆ rlc_pathVertices gamma.1)
  (hlVerts : rlc_pathVertices delta'.1 ⊆ rlc_pathVertices gamma'.1)
  (hactive : (rlc_extremalPairCandidate (gamma, gamma')).Nonempty) :
-- imply
  RlcBookFaithfulStratumReplacement gamma gamma' delta delta' := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulStratumReplacement.of_subpaths hfaith hrEdges hlEdges hrVerts hlVerts hactive

/--
[RlcBookFaithfulStratumReplacement.extremalPairCandidateEdges_disjoint_connectorEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma extremalPairCandidateEdges_disjoint_connectorEdges_eq_2
  {n : Int}
  {gamma delta : RlcRightDiagonalPath n}
  {gamma' delta' : RlcLeftDiagonalPath n}
  {R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta'} :
-- imply
  Disjoint (rlc_extremalPairCandidateEdges (gamma, gamma')) (rlc_connectorEdges delta delta') := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulStratumReplacement.extremalPairCandidateEdges_disjoint_connectorEdges R

/--
[RlcBookFaithfulTracePair.finiteExtremalPairCandidateEdges_disjoint_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma finiteExtremalPairCandidateEdges_disjoint_connector_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  Disjoint (rlc_finiteExtremalPairCandidateEdges gamma gamma') (rlc_connectorFiniteGraph gamma gamma').edgeFinset := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.finiteExtremalPairCandidateEdges_disjoint_connector hfaith

/--
[RlcBookFaithfulStratumReplacement.finiteExtremalPairCandidateEdges_disjoint_connector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma finiteExtremalPairCandidateEdges_disjoint_connector_eq_2
  {n : Int}
  {gamma delta : RlcRightDiagonalPath n}
  {gamma' delta' : RlcLeftDiagonalPath n}
  {R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta'} :
-- imply
  Disjoint (rlc_finiteExtremalPairCandidateEdges gamma gamma') (rlc_connectorFiniteGraph delta delta').edgeFinset := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulStratumReplacement.finiteExtremalPairCandidateEdges_disjoint_connector R

/--
[RlcBookFaithfulStratumReplacement.finiteExtremalPairCandidate_trace_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma finiteExtremalPairCandidate_trace_open_eq
  {n : Int}
  {gamma delta : RlcRightDiagonalPath n}
  {gamma' delta' : RlcLeftDiagonalPath n}
  {R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta'}
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hpsi : psi ∈ rlc_finiteExtremalPairCandidate gamma gamma') :
-- imply
  ∀ e ∈ (rlc_connectorTraceWiring delta delta').edgeFinset, psi e = true := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulStratumReplacement.finiteExtremalPairCandidate_trace_open R hpsi

/--
[RlcBookFaithfulStratumReplacement.compatibleExteriorFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma compatibleExteriorFibre_eq
  {n : Int}
  {gamma delta : RlcRightDiagonalPath n}
  {gamma' delta' : RlcLeftDiagonalPath n}
  {R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta'}
  {H : SimpleGraph (RlcConnectorVertex n)}
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hGH : rlc_connectorFiniteGraph delta delta' ≤ H)
  (hTH : rlc_connectorTraceWiring delta delta' ≤ H)
  (hpsi : psi ∈ rlc_finiteExtremalPairCandidate gamma gamma') :
-- imply
  RlcConnectorCompatibleExteriorFibre delta delta' H psi where connector_le := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulStratumReplacement.compatibleExteriorFibre R H hGH hTH hpsi

/--
[rlc_finiteExtremalPairCandidate_compatibleExteriorFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_finiteExtremalPairCandidate_compatibleExteriorFibre_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H : SimpleGraph (RlcConnectorVertex n)}
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
  (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
  (hpsi : psi ∈ rlc_finiteExtremalPairCandidate gamma gamma') :
-- imply
  RlcConnectorCompatibleExteriorFibre gamma gamma' H psi where connector_le := by
-- proof
  apply StatMech.Universality.rlc_finiteExtremalPairCandidate_compatibleExteriorFibre gamma gamma' H hGH hTH hpsi

/--
[RlcSequentialExtremalExplorationState.toCompatibleExteriorFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma toCompatibleExteriorFibre_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {S : RlcSequentialExtremalExplorationState gamma gamma'}
  {H : SimpleGraph (RlcConnectorVertex n)}
-- given
  (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
  (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H) :
-- imply
  RlcConnectorCompatibleExteriorFibre gamma gamma' H (rlc_connectorRestrictConfig S.rawConfig) where connector_le := by
-- proof
  apply StatMech.Universality.RlcSequentialExtremalExplorationState.toCompatibleExteriorFibre S H hGH hTH

/--
[RlcConnectorCompatibleExteriorFibre.trace_le_frozenExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma trace_le_frozenExterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H : SimpleGraph (RlcConnectorVertex n)}
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {F : RlcConnectorCompatibleExteriorFibre gamma gamma' H psi}
  {B : SimpleGraph (RlcConnectorVertex n)} :
-- imply
  rlc_connectorTraceWiring gamma gamma' ≤ rlc_connectorFrozenExteriorGraph gamma gamma' H B psi := by
-- proof
  apply StatMech.Universality.RlcConnectorCompatibleExteriorFibre.trace_le_frozenExterior F B

/--
[RlcConnectorCompatibleExteriorFibre.separate_le_inducedWiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma separate_le_inducedWiring_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H : SimpleGraph (RlcConnectorVertex n)}
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {F : RlcConnectorCompatibleExteriorFibre gamma gamma' H psi}
  {B : SimpleGraph (RlcConnectorVertex n)} :
-- imply
  rlc_connectorSeparateWiring gamma gamma' ≤ rlc_connectorExteriorInducedWiring gamma gamma' H B psi := by
-- proof
  apply StatMech.Universality.RlcConnectorCompatibleExteriorFibre.separate_le_inducedWiring F B

/--
[rlc_connectorExteriorFibreConfig_agreesOff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorExteriorFibreConfig_agreesOff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet} :
-- imply
  FK.AgreesOff (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) := by
-- proof
  apply StatMech.Universality.rlc_connectorExteriorFibreConfig_agreesOff gamma gamma' psi eta

/--
[rlc_connectorExteriorFibreConfig_restrictActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorExteriorFibreConfig_restrictActive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet} :
-- imply
  FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) = eta := by
-- proof
  apply StatMech.Universality.rlc_connectorExteriorFibreConfig_restrictActive gamma gamma' psi eta

/--
[rlc_connectorExteriorFibreConfig_restrictActive_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorExteriorFibreConfig_restrictActive_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {psi rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hrho : FK.AgreesOff (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi rho) :
-- imply
  rlc_connectorExteriorFibreConfig gamma gamma' psi (FK.restrictActive (rlc_connectorFiniteGraph gamma gamma') rho) = rho := by
-- proof
  apply StatMech.Universality.rlc_connectorExteriorFibreConfig_restrictActive_eq gamma gamma' psi rho hrho

/--
[rlc_openSub_exteriorFibre_sup_frozen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_openSub_exteriorFibre_sup_frozen_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet}
-- given
  (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H) :
-- imply
  FK.openSub H (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) ⊔ B = FK.openSub (rlc_connectorFiniteGraph gamma gamma') (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta) ⊔ rlc_connectorFrozenExteriorGraph gamma gamma' H B psi := by
-- proof
  apply StatMech.Universality.rlc_openSub_exteriorFibre_sup_frozen gamma gamma' H B hGH psi eta

/--
[rlc_sup_frozen_reachable_iff_induced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_sup_frozen_reachable_iff_induced_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {A : SimpleGraph (RlcConnectorVertex n)}
  {x y : RlcConnectorVertex n} :
-- imply
  (A ⊔ rlc_connectorFrozenExteriorGraph gamma gamma' H B psi).Reachable x y ↔ (A ⊔ rlc_connectorExteriorInducedWiring gamma gamma' H B psi).Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_sup_frozen_reachable_iff_induced gamma gamma' H B psi A x y

/--
[rlc_numClustersBC_exteriorFibre_eq_induced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_numClustersBC_exteriorFibre_eq_induced_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet}
-- given
  (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H) :
-- imply
  FK.numClustersBC H B (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) = FK.numClustersBC (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorExteriorInducedWiring gamma gamma' H B psi) (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta) := by
-- proof
  apply StatMech.Universality.rlc_numClustersBC_exteriorFibre_eq_induced gamma gamma' H B hGH psi eta

/--
[rlc_edgeProduct_exteriorFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_edgeProduct_exteriorFibre_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p : Real}
  {eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet}
-- given
  (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H) :
-- imply
  FK.edgeProduct H p (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) = rlc_connectorExteriorEdgeFactor gamma gamma' H psi p * FK.edgeProduct (rlc_connectorFiniteGraph gamma gamma') p (FK.extendActive (rlc_connectorFiniteGraph gamma gamma') eta) := by
-- proof
  apply StatMech.Universality.rlc_edgeProduct_exteriorFibre gamma gamma' H hGH psi p eta

/--
[rlc_bcWeight_exteriorFibre_eq_induced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_bcWeight_exteriorFibre_eq_induced_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p q : Real}
  {eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet}
-- given
  (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H) :
-- imply
  FK.bcWeight H B p q (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) = rlc_connectorExteriorEdgeFactor gamma gamma' H psi p * FK.activeBCWeight (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorExteriorInducedWiring gamma gamma' H B psi) (fun _ => p) q eta := by
-- proof
  apply StatMech.Universality.rlc_bcWeight_exteriorFibre_eq_induced gamma gamma' H B hGH psi p q eta

/--
[rlc_connectorExteriorFibre_inducedBcZ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorExteriorFibre_inducedBcZ_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p q : Real}
-- given
  (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H) :
-- imply
  FK.inducedBcZ H B p q (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi = rlc_connectorExteriorEdgeFactor gamma gamma' H psi p * FK.activeBCZ (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorExteriorInducedWiring gamma gamma' H B psi) (fun _ => p) q := by
-- proof
  apply StatMech.Universality.rlc_connectorExteriorFibre_inducedBcZ_eq gamma gamma' H B hGH psi p q

/--
[rlc_connectorExteriorFibre_condBcProb_eq_induced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorExteriorFibre_condBcProb_eq_induced_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p q : Real}
  {eta : ConfigSpace (rlc_connectorFiniteGraph gamma gamma').edgeSet}
-- given
  (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  FK.condBcProb H B p q (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi (rlc_connectorExteriorFibreConfig gamma gamma' psi eta) = FK.activeBCProb (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorExteriorInducedWiring gamma gamma' H B psi) (fun _ => p) q eta := by
-- proof
  apply StatMech.Universality.rlc_connectorExteriorFibre_condBcProb_eq_induced gamma gamma' H B hGH psi hp hp1 eta

/--
[rlc_connectorExteriorFibreCondEventMass_eq_activeInduced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorExteriorFibreCondEventMass_eq_activeInduced_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p q : Real}
-- given
  (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  rlc_connectorExteriorFibreCondEventMass gamma gamma' H B psi p q = FK.activeBCProbOf (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorExteriorInducedWiring gamma gamma' H B psi) (fun _ => p) q (rlc_connectorActiveEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorExteriorFibreCondEventMass_eq_activeInduced gamma gamma' H B hGH psi hp hp1

/--
[rlc_connectorExteriorFibreCondEventMass_eq_induced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorExteriorFibreCondEventMass_eq_induced_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p q : Real}
-- given
  (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  rlc_connectorExteriorFibreCondEventMass gamma gamma' H B psi p q = FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorExteriorInducedWiring gamma gamma' H B psi) p q (rlc_finiteConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_connectorExteriorFibreCondEventMass_eq_induced gamma gamma' H B hGH psi hp hp1 hq

/--
[rlc_connectorExteriorFibreCondEventMass_eq_ambientSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorExteriorFibreCondEventMass_eq_ambientSum_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {p q : Real} :
-- imply
  rlc_connectorExteriorFibreCondEventMass gamma gamma' H B psi p q = ∑ rho, (rlc_finiteConnectorEvent gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.condBcProb H B p q (rlc_connectorFiniteGraph gamma gamma').edgeFinset psi rho := by
-- proof
  apply StatMech.Universality.rlc_connectorExteriorFibreCondEventMass_eq_ambientSum gamma gamma' H B psi p q

/--
[rlc_connectorExteriorFibreCondEventMass_ge_separate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorExteriorFibreCondEventMass_ge_separate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {F : RlcConnectorCompatibleExteriorFibre gamma gamma' H psi}
  {q : Real}
-- given
  (hq : 1 ≤ q) :
-- imply
  FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') ≤ rlc_connectorExteriorFibreCondEventMass gamma gamma' H B psi (BeffaraDC.selfDualPoint q) q := by
-- proof
  apply StatMech.Universality.rlc_connectorExteriorFibreCondEventMass_ge_separate gamma gamma' H B psi F hq

/--
[RlcSequentialExtremalExplorationState.connectorConditionalMass_ge_separate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma connectorConditionalMass_ge_separate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {S : RlcSequentialExtremalExplorationState gamma gamma'}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {q : Real}
-- given
  (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
  (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
  (hq : 1 ≤ q) :
-- imply
  FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') ≤ rlc_connectorExteriorFibreCondEventMass gamma gamma' H B (rlc_connectorRestrictConfig S.rawConfig) (BeffaraDC.selfDualPoint q) q := by
-- proof
  apply StatMech.Universality.RlcSequentialExtremalExplorationState.connectorConditionalMass_ge_separate S H B hGH hTH hq

/--
[rlc_connectorOutsideEventMass_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_connectorOutsideEventMass_lower_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {S : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))}
  {q : Real}
-- given
  (hS : FK.DependsOnOutside (rlc_connectorFiniteGraph gamma gamma').edgeFinset S)
  (hcompat : ∀ {psi}, psi ∈ S → RlcConnectorCompatibleExteriorFibre gamma gamma' H psi)
  (hq : 1 ≤ q) :
-- imply
  FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') * (∑ rho, S.indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤ ∑ rho, ((rlc_finiteConnectorEvent gamma gamma') ∩ S).indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
-- proof
  apply StatMech.Universality.rlc_connectorOutsideEventMass_lower gamma gamma' H B S hS hcompat hq

/--
[rlc_finiteExtremalPairCandidate_connectorMass_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma rlc_finiteExtremalPairCandidate_connectorMass_lower_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {q : Real}
-- given
  (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
  (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
  (hdisj : Disjoint (rlc_finiteExtremalPairCandidateEdges gamma gamma') (rlc_connectorFiniteGraph gamma gamma').edgeFinset)
  (hq : 1 ≤ q) :
-- imply
  FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') * (∑ rho, (rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤ ∑ rho, ((rlc_finiteConnectorEvent gamma gamma') ∩ rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
-- proof
  apply StatMech.Universality.rlc_finiteExtremalPairCandidate_connectorMass_lower gamma gamma' H B hGH hTH hdisj hq

/--
[RlcBookFaithfulStratumReplacement.finiteExtremalPairCandidate_connectorMass_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma finiteExtremalPairCandidate_connectorMass_lower_eq
  {n : Int}
  {gamma delta : RlcRightDiagonalPath n}
  {gamma' delta' : RlcLeftDiagonalPath n}
  {R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta'}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {q : Real}
-- given
  (hGH : rlc_connectorFiniteGraph delta delta' ≤ H)
  (hTH : rlc_connectorTraceWiring delta delta' ≤ H)
  (hq : 1 ≤ q) :
-- imply
  FK.bcEventMass (rlc_connectorFiniteGraph delta delta') (rlc_connectorSeparateWiring delta delta') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent delta delta') * (∑ rho, (rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤ ∑ rho, ((rlc_finiteConnectorEvent delta delta') ∩ rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulStratumReplacement.finiteExtremalPairCandidate_connectorMass_lower R H B hGH hTH hq

/--
[RlcBookFaithfulStratumReplacement.finiteExtremalPairCandidate_connectorMass_selfDual_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma finiteExtremalPairCandidate_connectorMass_selfDual_ge_eq
  {n : Int}
  {gamma delta : RlcRightDiagonalPath n}
  {gamma' delta' : RlcLeftDiagonalPath n}
  {R : RlcBookFaithfulStratumReplacement gamma gamma' delta delta'}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {q : Real}
-- given
  (hGH : rlc_connectorFiniteGraph delta delta' ≤ H)
  (hTH : rlc_connectorTraceWiring delta delta' ≤ H)
  (hq : 1 ≤ q)
  (hdual : rlc_connectorForcedDualEventMass delta delta' (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent delta delta')ᶜ ≤ FK.bcEventMass (rlc_connectorFiniteGraph delta delta') (rlc_connectorMergedWiring delta delta') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent delta delta')) :
-- imply
  1 / (1 + q) * (∑ rho, (rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤ ∑ rho, ((rlc_finiteConnectorEvent delta delta') ∩ rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulStratumReplacement.finiteExtremalPairCandidate_connectorMass_selfDual_ge R H B hGH hTH hq hdual

/--
[RlcBookFaithfulTracePair.finiteExtremalPairCandidate_connectorMass_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma finiteExtremalPairCandidate_connectorMass_lower_eq_2
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {q : Real}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
  (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
  (hq : 1 ≤ q) :
-- imply
  FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma') * (∑ rho, (rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤ ∑ rho, ((rlc_finiteConnectorEvent gamma gamma') ∩ rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.finiteExtremalPairCandidate_connectorMass_lower hfaith H B hGH hTH hq

/--
[RlcBookFaithfulTracePair.finiteExtremalPairCandidate_connectorMass_selfDual_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean)
-/
@[path]
private lemma finiteExtremalPairCandidate_connectorMass_selfDual_ge_eq_2
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {H B : SimpleGraph (RlcConnectorVertex n)}
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {q : Real}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hGH : rlc_connectorFiniteGraph gamma gamma' ≤ H)
  (hTH : rlc_connectorTraceWiring gamma gamma' ≤ H)
  (hq : 1 ≤ q)
  (hdual : rlc_connectorForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')ᶜ ≤ FK.bcEventMass (rlc_connectorFiniteGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteConnectorEvent gamma gamma')) :
-- imply
  1 / (1 + q) * (∑ rho, (rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho) ≤ ∑ rho, ((rlc_finiteConnectorEvent gamma gamma') ∩ rlc_finiteExtremalPairCandidate gamma gamma').indicator (fun _ => (1 : Real)) rho * FK.bcProb H B (BeffaraDC.selfDualPoint q) q rho := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.finiteExtremalPairCandidate_connectorMass_selfDual_ge hfaith H B hGH hTH hq hdual


-- created on 2026-10-23
