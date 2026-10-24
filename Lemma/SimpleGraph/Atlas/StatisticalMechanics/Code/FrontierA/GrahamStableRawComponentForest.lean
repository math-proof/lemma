import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[FiniteRankTerminalSystem.terminalClosure_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma terminalClosure_eq_eq
  [Fintype I]
  [DecidableEq I]
  [DecidableEq A]
  [DecidableEq B]
  {system : FiniteRankTerminalSystem A B}
  {a : A} :
-- imply
  system.terminalClosure a = system.terminals a ∪ (system.children a).attach.biUnion (fun child => system.terminalClosure child.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRankTerminalSystem.terminalClosure_eq system a

/--
[FiniteRankTerminalSystem.terminals_subset_terminalClosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma terminals_subset_terminalClosure_eq
  [Fintype I]
  [DecidableEq I]
  [DecidableEq A]
  [DecidableEq B]
  {system : FiniteRankTerminalSystem A B}
  {a : A} :
-- imply
  system.terminals a ⊆ system.terminalClosure a := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRankTerminalSystem.terminals_subset_terminalClosure system a

/--
[FiniteRankTerminalSystem.terminalClosure_subset_of_mem_children](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma terminalClosure_subset_of_mem_children_eq
  [Fintype I]
  [DecidableEq I]
  [DecidableEq A]
  [DecidableEq B]
  {system : FiniteRankTerminalSystem A B}
  {a child : A}
-- given
  (hchild : child ∈ system.children a) :
-- imply
  system.terminalClosure child ⊆ system.terminalClosure a := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRankTerminalSystem.terminalClosure_subset_of_mem_children system hchild

/--
[FiniteRankTerminalSystem.exists_terminalEmbedding_of_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_terminalEmbedding_of_hall_eq
  [Fintype I]
  [DecidableEq I]
  [DecidableEq A]
  [DecidableEq B]
  {system : FiniteRankTerminalSystem A B}
-- given
  (hhall : ∀ sources : Finset A, sources.card ≤ (sources.biUnion system.terminalClosure).card) :
-- imply
  ∃ matching : A ↪ B, ∀ source, system.ReachesTerminal source (matching source) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRankTerminalSystem.exists_terminalEmbedding_of_hall system hhall

/--
[exists_minimal_deficiency_one_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_minimal_deficiency_one_family_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  [Fintype B]
  [DecidableEq A]
  [DecidableEq B]
-- given
  (neighborhood : Finset A -> Finset B)
  (hmono : Monotone neighborhood)
  (hfail : ∃ sources : Finset A, (neighborhood sources).card < sources.card) :
-- imply
  ∃ sources : Finset A, sources.Nonempty ∧ (neighborhood sources).card + 1 = sources.card ∧ (∀ source ∈ sources, neighborhood (sources.erase source) = neighborhood sources) ∧ ∀ smaller : Finset A, smaller ⊂ sources -> smaller.card ≤ (neighborhood smaller).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_minimal_deficiency_one_family neighborhood hmono hfail

/--
[finiteBipartiteRelationNeighborhood_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteBipartiteRelationNeighborhood_mono_eq
  [Fintype I]
  [DecidableEq I]
  {A : Type u}
  {B : Type v}
  [Fintype B]
-- given
  (related : A -> B -> Prop) :
-- imply
  Monotone (finiteBipartiteRelationNeighborhood related) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteBipartiteRelationNeighborhood_mono related

/--
[FiniteRelationMinimalTightProblem.rank_eq_carrier_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma rank_eq_carrier_card_eq
  [Fintype I]
  [DecidableEq I]
  {problem : FiniteRelationMinimalTightProblem.{u, v}} :
-- imply
  problem.rank = problem.carrier.card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRelationMinimalTightProblem.rank_eq_carrier_card problem

/--
[FiniteRelationMinimalTightProblem.strongInduction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma strongInduction_eq
  [Fintype I]
  [DecidableEq I]
  {problem : FiniteRelationMinimalTightProblem.{u, v}}
-- given
  (motive : FiniteRelationMinimalTightProblem.{u, v} -> Prop)
  (step : ∀ problem, (∀ smaller, smaller.rank < problem.rank -> motive smaller) -> motive problem) :
-- imply
  motive problem := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRelationMinimalTightProblem.strongInduction motive step problem

/--
[FiniteRelationMinimalTightProblem.tokenCarrier_card_lt_stateCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma tokenCarrier_card_lt_stateCarrier_eq
  [Fintype I]
  [DecidableEq I]
  {problem : FiniteRelationMinimalTightProblem.{u, v}} :
-- imply
  Fintype.card problem.TokenCarrier < Fintype.card problem.StateCarrier := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRelationMinimalTightProblem.tokenCarrier_card_lt_stateCarrier problem

/--
[FiniteRelationMinimalTightProblem.exists_holeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_holeState_eq
  [Fintype I]
  [DecidableEq I]
  {problem : FiniteRelationMinimalTightProblem.{u, v}} :
-- imply
  Nonempty (StatMech.FrontierA.RelationPartialMatching.HoleState problem.restrictedIncident) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRelationMinimalTightProblem.exists_holeState problem

/--
[FiniteRelationMinimalTightProblem.strongInductionWithHoleState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma strongInductionWithHoleState_eq
  [Fintype I]
  [DecidableEq I]
  {problem : FiniteRelationMinimalTightProblem.{u, v}}
-- given
  (motive : FiniteRelationMinimalTightProblem.{u, v} -> Prop)
  (step : ∀ problem, Nonempty (StatMech.FrontierA.RelationPartialMatching.HoleState problem.restrictedIncident) -> (∀ smaller, smaller.rank < problem.rank -> motive smaller) -> motive problem) :
-- imply
  motive problem := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRelationMinimalTightProblem.strongInductionWithHoleState motive step problem

/--
[exists_external_incident_of_tight_properHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_external_incident_of_tight_properHall_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  [Fintype B]
  [DecidableEq A]
  [DecidableEq B]
  [DecidableRel related]
  {size : Nat}
  {states : Fin size ↪ A}
  {tokens : Fin size ↪ B}
-- given
  (related : A -> B -> Prop)
  (htight : Fintype.card B + 1 = Fintype.card A)
  (hproper : ∀ smaller : Finset A, smaller ⊂ Finset.univ -> smaller.card ≤ (Finset.univ.filter fun token => ∃ source ∈ smaller, related source token).card)
  (hsize : 0 < size) :
-- imply
  ∃ i : Fin size, ∃ source : A, (∀ q, source ≠ states q) ∧ related source (tokens i) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_external_incident_of_tight_properHall related htight hproper size hsize states tokens

/--
[finiteEmbedding_add_fresh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteEmbedding_add_fresh_eq
  [Fintype I]
  [DecidableEq I]
  {size : Nat}
  {block : Fin size ↪ A}
  {extra : A}
-- given
  (hfresh : ∀ i, extra ≠ block i) :
-- imply
  Nonempty (Fin (size + 1) ↪ A) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteEmbedding_add_fresh size block extra hfresh

/--
[finiteEmbedding_snoc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteEmbedding_snoc_eq
  [Fintype I]
  [DecidableEq I]
  {size : Nat}
  {block : Fin size ↪ A}
  {extra : A}
-- given
  (hfresh : ∀ i, extra ≠ block i) :
-- imply
  ∃ extended : Fin (size + 1) ↪ A, (∀ i, extended i.castSucc = block i) ∧ extended (Fin.last size) = extra := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteEmbedding_snoc size block extra hfresh

/--
[finiteEmbedding_replaceAt_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteEmbedding_replaceAt_same_eq
  [Fintype I]
  [DecidableEq I]
  {size : Nat}
  {block : Fin size ↪ A}
  {extra : A}
  {index : Fin size}
-- given
  (hfresh : ∀ i, extra ≠ block i) :
-- imply
  finiteEmbedding_replaceAt block extra hfresh index index = extra := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteEmbedding_replaceAt_same block extra hfresh index

/--
[finiteEmbedding_replaceAt_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteEmbedding_replaceAt_ne_eq
  [Fintype I]
  [DecidableEq I]
  {size : Nat}
  {block : Fin size ↪ A}
  {extra : A}
  {index other : Fin size}
-- given
  (hfresh : ∀ i, extra ≠ block i)
  (hne : other ≠ index) :
-- imply
  finiteEmbedding_replaceAt block extra hfresh index other = block other := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteEmbedding_replaceAt_ne block extra hfresh index other hne

/--
[finiteEmbedding_replaceAt_displaced_fresh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteEmbedding_replaceAt_displaced_fresh_eq
  [Fintype I]
  [DecidableEq I]
  {size : Nat}
  {block : Fin size ↪ A}
  {extra : A}
  {index : Fin size}
-- given
  (hfresh : ∀ i, extra ≠ block i) :
-- imply
  ∀ other, block index ≠ finiteEmbedding_replaceAt block extra hfresh index other := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteEmbedding_replaceAt_displaced_fresh block extra hfresh index

/--
[exists_fin_castSucc_eq_of_ne_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_fin_castSucc_eq_of_ne_last_eq
  [Fintype I]
  [DecidableEq I]
  {size : Nat}
  {q : Fin (size + 1)}
-- given
  (hq : q ≠ Fin.last size) :
-- imply
  ∃ i : Fin size, i.castSucc = q := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_fin_castSucc_eq_of_ne_last q hq

/--
[exists_fin_castSucc_eq_left_or_right_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_fin_castSucc_eq_left_or_right_of_ne_eq
  [Fintype I]
  [DecidableEq I]
  {size : Nat}
  {q r : Fin (size + 1)}
-- given
  (hqr : q ≠ r) :
-- imply
  ∃ i : Fin size, i.castSucc = q ∨ i.castSucc = r := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_fin_castSucc_eq_left_or_right_of_ne q r hqr

/--
[saturatedHoleState_sourceEmbedding_add_hole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma saturatedHoleState_sourceEmbedding_add_hole_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  {r : A -> B -> Prop}
  {state : StatMech.FrontierA.RelationPartialMatching.HoleState r}
  {size : Nat}
  {tokens : Fin size ↪ B}
-- given
  (hsaturated : ∀ token, ∃ source, state.matching.toFun source = some token) :
-- imply
  Nonempty (Fin (size + 1) ↪ A) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.saturatedHoleState_sourceEmbedding_add_hole state hsaturated size tokens

/--
[saturatedHoleState_targetPreimage_fresh_of_token_fresh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma saturatedHoleState_targetPreimage_fresh_of_token_fresh_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  {r : A -> B -> Prop}
  {state : StatMech.FrontierA.RelationPartialMatching.HoleState r}
  {size : Nat}
  {sources : Fin size ↪ A}
  {tokens : Fin size ↪ B}
  {fresh : B}
-- given
  (hsaturated : ∀ token, ∃ source, state.matching.toFun source = some token)
  (hmatched : ∀ i, state.matching.toFun (sources i) = some (tokens i))
  (hfresh : ∀ i, fresh ≠ tokens i) :
-- imply
  ∀ i, state.matching.targetPreimage hsaturated fresh ≠ sources i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.saturatedHoleState_targetPreimage_fresh_of_token_fresh state hsaturated size sources tokens hmatched fresh hfresh

/--
[saturatedHoleState_extendMatchedBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma saturatedHoleState_extendMatchedBlock_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  {r : A -> B -> Prop}
  {state : StatMech.FrontierA.RelationPartialMatching.HoleState r}
  {size : Nat}
  {sources : Fin size ↪ A}
  {tokens : Fin size ↪ B}
  {fresh : B}
-- given
  (hsaturated : ∀ token, ∃ source, state.matching.toFun source = some token)
  (hmatched : ∀ i, state.matching.toFun (sources i) = some (tokens i))
  (hfresh : ∀ i, fresh ≠ tokens i) :
-- imply
  ∃ extendedSources : (Fin size ⊕ Fin 1) ↪ A, ∃ extendedTokens : (Fin size ⊕ Fin 1) ↪ B, (∀ q, state.matching.toFun (extendedSources q) = some (extendedTokens q)) ∧ (∀ i, extendedSources (Sum.inl i) = sources i) ∧ (∀ i, extendedTokens (Sum.inl i) = tokens i) ∧ extendedTokens (Sum.inr 0) = fresh := by
-- proof
  apply StatMech.GrahamGHS.FourColor.saturatedHoleState_extendMatchedBlock state hsaturated size sources tokens hmatched fresh hfresh

/--
[saturatedHoleState_alternatingPath_nextSource_fresh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma saturatedHoleState_alternatingPath_nextSource_fresh_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  {r : A -> B -> Prop}
  {state : StatMech.FrontierA.RelationPartialMatching.HoleState r}
  {size : Nat}
  {sources : Fin (size + 1) ↪ A}
  {tokens : Fin size ↪ B}
  {fresh : B}
-- given
  (hsaturated : ∀ token, ∃ source, state.matching.toFun source = some token)
  (hhole : sources 0 = state.hole)
  (hmatched : ∀ i, state.matching.toFun (sources i.succ) = some (tokens i))
  (hfresh : ∀ i, fresh ≠ tokens i) :
-- imply
  ∀ q, state.matching.targetPreimage hsaturated fresh ≠ sources q := by
-- proof
  apply StatMech.GrahamGHS.FourColor.saturatedHoleState_alternatingPath_nextSource_fresh state hsaturated size sources tokens hhole hmatched fresh hfresh

/--
[saturatedHoleState_alternatingPath_close_or_extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma saturatedHoleState_alternatingPath_close_or_extend_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  {r : A -> B -> Prop}
  {state : StatMech.FrontierA.RelationPartialMatching.HoleState r}
  {size : Nat}
  {sources : Fin (size + 1) ↪ A}
  {tokens : Fin size ↪ B}
-- given
  (hsaturated : ∀ token, ∃ source, state.matching.toFun source = some token)
  (successor : A -> B)
  (hhole : sources 0 = state.hole)
  (htransition : ∀ i, tokens i = successor (sources i.castSucc))
  (hmatched : ∀ i, state.matching.toFun (sources i.succ) = some (tokens i)) :
-- imply
  (∃ i, successor (sources (Fin.last size)) = tokens i ∧ state.matching.targetPreimage hsaturated (successor (sources (Fin.last size))) = sources i.succ) ∨ ∃ extendedSources : Fin (size + 2) ↪ A, ∃ extendedTokens : Fin (size + 1) ↪ B, extendedSources 0 = state.hole ∧ (∀ i, extendedTokens i = successor (extendedSources i.castSucc)) ∧ (∀ i, state.matching.toFun (extendedSources i.succ) = some (extendedTokens i)) ∧ (∀ i, extendedSources i.castSucc = sources i) ∧ (∀ i, extendedTokens i.castSucc = tokens i) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.saturatedHoleState_alternatingPath_close_or_extend state hsaturated successor size sources tokens hhole htransition hmatched

/--
[finiteEmbeddingComplement_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteEmbeddingComplement_card_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  [DecidableEq A]
  {size : Nat}
  {block : Fin size ↪ A} :
-- imply
  Fintype.card (FiniteEmbeddingComplement size block) = Fintype.card A - size := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteEmbeddingComplement_card size block

/--
[finiteRelationComplement_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteRelationComplement_closed_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  [DecidableEq A]
  [Fintype B]
  [DecidableEq B]
  {size : Nat}
  {sources : Fin size ↪ A}
  {tokens : Fin size ↪ B}
  {source : FiniteEmbeddingComplement size sources}
  {token : B}
-- given
  (related : A -> B -> Prop)
  (hclosed : FiniteRelationBlockClosed related size sources tokens)
  (hrelated : related source.1 token) :
-- imply
  token ∉ finiteEmbeddingBlock size tokens := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteRelationComplement_closed related size sources tokens hclosed source token hrelated

/--
[finiteRelationBlockClosed_or_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteRelationBlockClosed_or_crossing_eq
  [Fintype I]
  [DecidableEq I]
  {size : Nat}
  {sources : Fin size ↪ A}
  {tokens : Fin size ↪ B}
-- given
  (related : A -> B -> Prop) :
-- imply
  FiniteRelationBlockClosed related size sources tokens ∨ ∃ source token, related source token ∧ (((∃ i, source = sources i) ∧ ∀ i, token ≠ tokens i) ∨ ((∀ i, source ≠ sources i) ∧ ∃ i, token = tokens i)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteRelationBlockClosed_or_crossing related size sources tokens

/--
[finiteRelationTokenClosed_or_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteRelationTokenClosed_or_crossing_eq
  [Fintype I]
  [DecidableEq I]
  {size : Nat}
  {sources : Fin size ↪ A}
  {tokens : Fin size ↪ B}
-- given
  (related : A -> B -> Prop) :
-- imply
  FiniteRelationTokenClosed related size sources tokens ∨ ∃ source token, related source token ∧ (∀ i, source ≠ sources i) ∧ ∃ i, token = tokens i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteRelationTokenClosed_or_crossing related size sources tokens

/--
[finiteRelationComplement_tokenClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteRelationComplement_tokenClosed_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  [DecidableEq A]
  [Fintype B]
  [DecidableEq B]
  {size : Nat}
  {sources : Fin size ↪ A}
  {tokens : Fin size ↪ B}
  {source : FiniteEmbeddingComplement size sources}
  {token : B}
-- given
  (related : A -> B -> Prop)
  (hclosed : FiniteRelationTokenClosed related size sources tokens)
  (hrelated : related source.1 token) :
-- imply
  token ∉ finiteEmbeddingBlock size tokens := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteRelationComplement_tokenClosed related size sources tokens hclosed source token hrelated

/--
[FiniteRelationDeficiencyOneFamily.tokenSaturated_or_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma tokenSaturated_or_crossing_eq
  [Fintype I]
  [DecidableEq I]
  [DecidableEq A]
  [DecidableEq B]
  {family : FiniteRelationDeficiencyOneFamily A B}
-- given
  (related : A -> B -> Prop) :
-- imply
  family.TokenSaturated related ∨ ∃ source token, related source token ∧ token ∈ family.tokens ∧ source ∉ family.states := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRelationDeficiencyOneFamily.tokenSaturated_or_crossing related family

/--
[FiniteRelationDeficiencyOneFamily.sourceSaturated_or_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma sourceSaturated_or_crossing_eq
  [Fintype I]
  [DecidableEq I]
  [DecidableEq A]
  [DecidableEq B]
  {family : FiniteRelationDeficiencyOneFamily A B}
-- given
  (related : A -> B -> Prop) :
-- imply
  family.SourceSaturated related ∨ ∃ source token, related source token ∧ source ∈ family.states ∧ token ∉ family.tokens := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRelationDeficiencyOneFamily.sourceSaturated_or_crossing related family

/--
[FiniteRelationDeficiencyOneFamily.mem_states_extendPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma mem_states_extendPair_eq
  [Fintype I]
  [DecidableEq I]
  [DecidableEq A]
  [DecidableEq B]
  {family : FiniteRelationDeficiencyOneFamily A B}
  {source : A}
  {token : B}
-- given
  (hsource : source ∉ family.states)
  (htoken : token ∉ family.tokens) :
-- imply
  source ∈ (family.extendPair source token hsource htoken).states := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRelationDeficiencyOneFamily.mem_states_extendPair family source token hsource htoken

/--
[FiniteRelationDeficiencyOneFamily.mem_tokens_extendPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma mem_tokens_extendPair_eq
  [Fintype I]
  [DecidableEq I]
  [DecidableEq A]
  [DecidableEq B]
  {family : FiniteRelationDeficiencyOneFamily A B}
  {source : A}
  {token : B}
-- given
  (hsource : source ∉ family.states)
  (htoken : token ∉ family.tokens) :
-- imply
  token ∈ (family.extendPair source token hsource htoken).tokens := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRelationDeficiencyOneFamily.mem_tokens_extendPair family source token hsource htoken

/--
[FiniteRelationCrossingContinuation.natural_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma natural_incident_eq
  [Fintype I]
  [DecidableEq I]
  {A : Type u}
  {B : Type v}
  {related : A -> B -> Prop}
  {continuation : FiniteRelationCrossingContinuation related} :
-- imply
  ∀ state, continuation.incident state (continuation.natural state) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRelationCrossingContinuation.natural_incident continuation

/--
[FiniteRelationCrossingContinuation.initialMatching_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma initialMatching_support_eq
  [Fintype I]
  [DecidableEq I]
  {A : Type u}
  {B : Type v}
  {related : A -> B -> Prop}
  {continuation : FiniteRelationCrossingContinuation related} :
-- imply
  continuation.initialMatching.support = Finset.univ.erase (Sum.inl continuation.index) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRelationCrossingContinuation.initialMatching_support continuation

/--
[FiniteRelationCrossingContinuation.initialMatching_maximum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma initialMatching_maximum_eq
  [Fintype I]
  [DecidableEq I]
  {A : Type u}
  {B : Type v}
  {related : A -> B -> Prop}
  {continuation : FiniteRelationCrossingContinuation related} :
-- imply
  continuation.initialMatching.IsMaximum := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRelationCrossingContinuation.initialMatching_maximum continuation

/--
[FiniteRelationCrossingContinuation.move_initialHole_eq_extra](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma move_initialHole_eq_extra_eq
  [Fintype I]
  [DecidableEq I]
  {A : Type u}
  {B : Type v}
  {related : A -> B -> Prop}
  {continuation : FiniteRelationCrossingContinuation related} :
-- imply
  (continuation.initialHoleState.move continuation.natural continuation.natural_incident).hole = Sum.inr () := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRelationCrossingContinuation.move_initialHole_eq_extra continuation

/--
[FiniteRelationCrossingContinuation.moveThenAlternate_hole](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma moveThenAlternate_hole_eq
  [Fintype I]
  [DecidableEq I]
  {A : Type u}
  {B : Type v}
  {related : A -> B -> Prop}
  {continuation : FiniteRelationCrossingContinuation related}
  {alternate : continuation.Token}
-- given
  (hne : alternate ≠ continuation.index)
  (hincident : continuation.incident (Sum.inr ()) alternate) :
-- imply
  let moved := continuation.initialHoleState.move continuation.natural continuation.natural_incident ∃ hincident' : continuation.incident moved.hole alternate, (moved.moveAcross alternate hincident').hole = Sum.inl alternate := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRelationCrossingContinuation.moveThenAlternate_hole continuation alternate hne hincident

/--
[FiniteRelationCrossingContinuation.exists_minimal_hole_repeat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_minimal_hole_repeat_eq
  [Fintype I]
  [DecidableEq I]
  {A : Type u}
  {B : Type v}
  {related : A -> B -> Prop}
  {continuation : FiniteRelationCrossingContinuation related} :
-- imply
  let move := StatMech.FrontierA.RelationPartialMatching.HoleState.move continuation.natural continuation.natural_incident ∃ start stop : Nat, start < stop ∧ stop ≤ continuation.size + 1 ∧ (move^[start] continuation.initialHoleState).hole = (move^[stop] continuation.initialHoleState).hole ∧ ∀ a b : Nat, a < b -> b < stop -> (move^[a] continuation.initialHoleState).hole ≠ (move^[b] continuation.initialHoleState).hole := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiniteRelationCrossingContinuation.exists_minimal_hole_repeat continuation

/--
[finiteRelation_threeTwoOrbitCore_saturated_no_freshToken](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteRelation_threeTwoOrbitCore_saturated_no_freshToken_eq
  [Fintype I]
  [DecidableEq I] :
-- imply
  let related : Fin 3 -> Fin 2 -> Prop := fun _ _ => True let family := FiniteRelationDeficiencyOneFamily.threeTwo (0 : Fin 3) 1 2 (by decide) (by decide) (by decide) (0 : Fin 2) 1 (by decide) family.IsSaturated related ∧ related 0 0 ∧ related 1 0 ∧ related 0 1 ∧ related 2 1 ∧ Nonempty (Fin 2 ↪ Fin 2) ∧ Nonempty (Fin 2 ↪ Fin 2) ∧ ¬ ∃ token : Fin 2, token ∉ family.tokens := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteRelation_threeTwoOrbitCore_saturated_no_freshToken

/--
[finiteRelation_threeTwoOrbitCore_balancedBlock_not_tokenClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteRelation_threeTwoOrbitCore_balancedBlock_not_tokenClosed_eq
  [Fintype I]
  [DecidableEq I] :
-- imply
  ∃ sources : Fin 1 ↪ Fin 3, ∃ tokens : Fin 1 ↪ Fin 2, ¬ FiniteRelationTokenClosed (fun _ _ => True) 1 sources tokens := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteRelation_threeTwoOrbitCore_balancedBlock_not_tokenClosed

/--
[finiteEmbeddingComplement_strictDeficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteEmbeddingComplement_strictDeficit_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  [DecidableEq A]
  [Fintype B]
  [DecidableEq B]
  {size : Nat}
  {sources : Fin size ↪ A}
  {tokens : Fin size ↪ B}
-- given
  (hdeficit : Fintype.card B < Fintype.card A) :
-- imply
  Fintype.card (FiniteEmbeddingComplement size tokens) < Fintype.card (FiniteEmbeddingComplement size sources) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteEmbeddingComplement_strictDeficit size sources tokens hdeficit

/--
[finiteEmbedding_strictBlock_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteEmbedding_strictBlock_prefix_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype B]
  [DecidableEq B]
  {size : Nat}
  {tokens : Fin (size + 1) ↪ B} :
-- imply
  ∃ initial : Fin size ↪ B, ∃ extra : FiniteEmbeddingComplement size initial, extra.1 = tokens (Fin.last size) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteEmbedding_strictBlock_prefix size tokens

/--
[exists_closedBlock_of_strictExtension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_closedBlock_of_strictExtension_eq
  [Fintype I]
  [DecidableEq I]
  {capacity : Nat}
  {start : Block}
-- given
  (blockSize : Block -> Nat)
  (closed : Block -> Prop)
  (hbound : ∀ block, blockSize block ≤ capacity)
  (hextend : ∀ block, ¬ closed block -> ∃ extended, blockSize extended = blockSize block + 1) :
-- imply
  ∃ block, closed block := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_closedBlock_of_strictExtension capacity blockSize closed hbound hextend start

/--
[exists_sizeMaximalBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_sizeMaximalBlock_eq
  [Fintype I]
  [DecidableEq I]
  {capacity : Nat}
  {start : Block}
-- given
  (blockSize : Block -> Nat)
  (hbound : ∀ block, blockSize block ≤ capacity) :
-- imply
  ∃ block, ∀ other, blockSize other ≤ blockSize block := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_sizeMaximalBlock capacity blockSize hbound start

/--
[exists_fintype_score_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_fintype_score_maximal_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  [Nonempty A]
-- given
  (score : A -> Nat) :
-- imply
  ∃ best, ∀ other, score other ≤ score best := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_fintype_score_maximal score

/--
[finiteEmbedding_three_of_pairwise_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteEmbedding_three_of_pairwise_ne_eq
  [Fintype I]
  [DecidableEq I]
  {a b c : A}
-- given
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c) :
-- imply
  Nonempty (Fin 3 ↪ A) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteEmbedding_three_of_pairwise_ne a b c hab hac hbc

/--
[finiteEmbedding_two_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma finiteEmbedding_two_of_ne_eq
  [Fintype I]
  [DecidableEq I]
  {a b : A}
-- given
  (hab : a ≠ b) :
-- imply
  Nonempty (Fin 2 ↪ A) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.finiteEmbedding_two_of_ne a b hab

/--
[tightProperHall_externalSource_freshToken_or_exhausts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma tightProperHall_externalSource_freshToken_or_exhausts_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  [Fintype B]
  [DecidableEq A]
  [DecidableEq B]
  [DecidableRel related]
  {size : Nat}
  {states : Fin size ↪ A}
  {external : A}
-- given
  (related : A -> B -> Prop)
  (hproper : ∀ smaller : Finset A, smaller ⊂ Finset.univ -> smaller.card ≤ (Finset.univ.filter fun token => ∃ source ∈ smaller, related source token).card)
  (hexternal : ∀ i, external ≠ states i) :
-- imply
  Nonempty (Fin (size + 1) ↪ B) ∨ ∀ source : A, source = external ∨ ∃ i, source = states i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.tightProperHall_externalSource_freshToken_or_exhausts related hproper size states external hexternal

/--
[strictDeficit_sub_balancedBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma strictDeficit_sub_balancedBlock_eq
  [Fintype I]
  [DecidableEq I]
  {self direct token block : Nat}
-- given
  (hblockDirect : block ≤ direct)
  (hblockToken : block ≤ token)
  (hdeficit : token < self + direct) :
-- imply
  token - block < self + (direct - block) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.strictDeficit_sub_balancedBlock self direct token block hblockDirect hblockToken hdeficit

/--
[strictDeficit_sub_balancedEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma strictDeficit_sub_balancedEmbeddings_eq
  [Fintype I]
  [DecidableEq I]
  [Finite Self]
  [Finite Direct]
  [Finite Token]
  {block : Nat}
  {directBlock : Nonempty (Fin block ↪ Direct)}
  {tokenBlock : Nonempty (Fin block ↪ Token)}
-- given
  (hdeficit : Nat.card Token < Nat.card Self + Nat.card Direct) :
-- imply
  Nat.card Token - block < Nat.card Self + (Nat.card Direct - block) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.strictDeficit_sub_balancedEmbeddings block hdeficit directBlock tokenBlock

/--
[exists_partialForest_terminal_or_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_partialForest_terminal_or_cycle_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  {start : A}
-- given
  (step : A -> A ⊕ B) :
-- imply
  (∃ n ≤ Fintype.card A, ∃ terminal, step ((partialForestAdvance step)^[n] start) = Sum.inr terminal) ∨ ∃ i j : Nat, i < j ∧ j ≤ Fintype.card A ∧ ((partialForestAdvance step)^[i] start) = ((partialForestAdvance step)^[j] start) ∧ ∀ n < j, ∃ next, step ((partialForestAdvance step)^[n] start) = Sum.inl next := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_partialForest_terminal_or_cycle step start

/--
[exists_function_iterate_repeat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_function_iterate_repeat_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  {start : A}
-- given
  (next : A -> A) :
-- imply
  ∃ i j : Nat, i < j ∧ j ≤ Fintype.card A ∧ next^[i] start = next^[j] start := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_function_iterate_repeat next start

/--
[partialForest_iterate_injective_through_first_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma partialForest_iterate_injective_through_first_terminal_eq
  [Fintype I]
  [DecidableEq I]
  {start : A}
  {stop : Nat}
-- given
  (step : A -> A ⊕ B)
  (hterminal : ∃ terminal, step ((partialForestAdvance step)^[stop] start) = Sum.inr terminal)
  (hfirst : ∀ n < stop, ∀ terminal, step ((partialForestAdvance step)^[n] start) ≠ Sum.inr terminal) :
-- imply
  Function.Injective fun i : Fin (stop + 1) => (partialForestAdvance step)^[i.1] start := by
-- proof
  apply StatMech.GrahamGHS.FourColor.partialForest_iterate_injective_through_first_terminal step start stop hterminal hfirst

/--
[exists_partialForest_terminal_or_rankDrop_or_maxRankCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_partialForest_terminal_or_rankDrop_or_maxRankCycle_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  {start : A}
-- given
  (step : A -> A ⊕ B)
  (rank : A -> Nat)
  (hmax : ∀ a, rank a ≤ rank start) :
-- imply
  (∃ n ≤ Fintype.card A, ∃ terminal, step ((partialForestAdvance step)^[n] start) = Sum.inr terminal) ∨ (∃ n < Fintype.card A, ∃ next, step ((partialForestAdvance step)^[n] start) = Sum.inl next ∧ rank next < rank start) ∨ ∃ i j : Nat, i < j ∧ j ≤ Fintype.card A ∧ ((partialForestAdvance step)^[i] start) = ((partialForestAdvance step)^[j] start) ∧ ∀ n < j, ∃ next, step ((partialForestAdvance step)^[n] start) = Sum.inl next ∧ rank next = rank start := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_partialForest_terminal_or_rankDrop_or_maxRankCycle step rank start hmax

/--
[map_iterate_eq_of_step_until](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma map_iterate_eq_of_step_until_eq
  [Fintype I]
  [DecidableEq I]
  {start : A}
  {length : Nat}
-- given
  (f : A -> A)
  (g : B -> B)
  (project : A -> B)
  (hstep : ∀ n < length, project (f ((f^[n]) start)) = g (project ((f^[n]) start))) :
-- imply
  project ((f^[length]) start) = (g^[length]) (project start) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.map_iterate_eq_of_step_until f g project start length hstep

/--
[exists_minimal_iterateKey_repeat_of_closedOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_minimal_iterateKey_repeat_of_closedOrbit_eq
  [Fintype I]
  [DecidableEq I]
  {start : A}
  {length : Nat}
-- given
  (f : A -> A)
  (key : A -> K)
  (hlength : 0 < length)
  (hrepeat : (f^[length] start) = start) :
-- imply
  ∃ first stop : Nat, first < stop ∧ stop ≤ length ∧ key (f^[first] start) = key (f^[stop] start) ∧ ∀ a b : Nat, a < b -> b < stop -> key (f^[a] start) ≠ key (f^[b] start) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_minimal_iterateKey_repeat_of_closedOrbit f key start length hlength hrepeat

/--
[exists_function_cycleEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_function_cycleEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  {start : A}
-- given
  (next : A -> A) :
-- imply
  ∃ size : Nat, 0 < size ∧ ∃ cycle : Fin size ↪ A, ∃ σ : Equiv.Perm (Fin size), ∀ i, cycle (σ i) = next (cycle i) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_function_cycleEmbedding next start

/--
[canonicalStableRawDirectAlternateExceptionalEdge_target_eq_next](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawDirectAlternateExceptionalEdge_target_eq_next_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdirect : s.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source)
  (hexceptional : CanonicalStableRawLeftTokenIsExceptional ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawDirectAlternateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hdirect)) :
-- imply
  (canonicalStableRawExceptionalEdgeOfLeftToken ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawDirectAlternateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hdirect) hexceptional).target = (canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno s).target := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawDirectAlternateExceptionalEdge_target_eq_next ends m j k l zero hloop hjk hkl hk0 p hno s hdirect hexceptional

/--
[canonicalStableRawDirectAlternateExceptionalEdge_next_or_sibling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawDirectAlternateExceptionalEdge_next_or_sibling_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdirect : s.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source)
  (hexceptional : CanonicalStableRawLeftTokenIsExceptional ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawDirectAlternateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hdirect)) :
-- imply
  let recovered := canonicalStableRawExceptionalEdgeOfLeftToken ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawDirectAlternateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hdirect) hexceptional let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno s recovered = next ∨ (recovered.source ≠ next.source ∧ recovered.target = next.target) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawDirectAlternateExceptionalEdge_next_or_sibling ends m j k l zero hloop hjk hkl hk0 p hno s hdirect hexceptional

/--
[canonicalStableRawReferenceOwnerLeftToken_rank_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawReferenceOwnerLeftToken_rank_lt_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  canonicalStableRawSourceRank ends m j k l zero p (canonicalStableRawReferenceOwnerLeftToken ends m j k l zero hloop hjk hkl hk0 p s hself).1 < canonicalStableRawSourceRank ends m j k l zero p s.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceOwnerLeftToken_rank_lt ends m j k l zero hloop hjk hkl hk0 p s hself

/--
[canonicalStableRawComponentAlternateToken_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentAlternateToken_incident_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {s : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component s (canonicalStableRawComponentAlternateToken ends m j k l zero hloop hjk hkl hk0 p hno component s) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentAlternateToken_incident ends m j k l zero hloop hjk hkl hk0 p hno component s

/--
[canonicalStableRawComponentAlternateToken_ne_natural](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentAlternateToken_ne_natural_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {s : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  canonicalStableRawComponentAlternateToken ends m j k l zero hloop hjk hkl hk0 p hno component s ≠ canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentAlternateToken_ne_natural ends m j k l zero hloop hjk hkl hk0 p hno component s

/--
[canonicalStableRawComponentSuccessorToken_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentSuccessorToken_incident_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {s : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component s (canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component s) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSuccessorToken_incident ends m j k l zero hloop hjk hkl hk0 p hno component s

/--
[canonicalStableRawComponentSuccessorToken_ne_natural](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentSuccessorToken_ne_natural_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {s : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component s ≠ canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSuccessorToken_ne_natural ends m j k l zero hloop hjk hkl hk0 p hno component s

/--
[canonicalStableRawComponentSuccessorToken_not_exceptional_of_ownerStable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentSuccessorToken_not_exceptional_of_ownerStable_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstable : CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
-- imply
  ¬ CanonicalStableRawLeftTokenIsExceptional ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component ⟨self.1, self.2.1⟩).1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSuccessorToken_not_exceptional_of_ownerStable ends m j k l zero hloop hjk hkl hk0 p hno component self hstable

/--
[canonicalStableRawComponentSuccessorToken_exceptional_of_advancing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentSuccessorToken_exceptional_of_advancing_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hadvancing : CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
-- imply
  CanonicalStableRawLeftTokenIsExceptional ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component ⟨self.1, self.2.1⟩).1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSuccessorToken_exceptional_of_advancing ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing

/--
[canonicalStableRawComponentDirectStateEquivExceptionalToken_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentDirectStateEquivExceptionalToken_apply_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  (canonicalStableRawComponentDirectStateEquivExceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component direct).1 = canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDirectStateEquivExceptionalToken_apply ends m j k l zero hloop hjk hkl hk0 p hno component direct

/--
[canonicalStableRawComponentNonexceptionalToken_ne_direct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentNonexceptionalToken_ne_direct_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component}
  {direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  terminal.1 ≠ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentNonexceptionalToken_ne_direct ends m j k l zero hloop hjk hkl hk0 p hno component terminal direct

/--
[canonicalStableRawComponentReferenceExceptionalDirect_rank_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceExceptionalDirect_rank_lt_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hexceptional : CanonicalStableRawLeftTokenIsExceptional ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentAlternateToken ends m j k l zero hloop hjk hkl hk0 p hno component ⟨self.1, self.2.1⟩).1) :
-- imply
  canonicalStableRawSourceRank ends m j k l zero p (canonicalStableRawComponentReferenceExceptionalDirect ends m j k l zero hloop hjk hkl hk0 p hno component self hexceptional).1.source < canonicalStableRawSourceRank ends m j k l zero p self.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceExceptionalDirect_rank_lt ends m j k l zero hloop hjk hkl hk0 p hno component self hexceptional

/--
[canonicalStableRawComponentExceptionalSuccessorDirect_natural](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentExceptionalSuccessorDirect_natural_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {s : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hexceptional : CanonicalStableRawLeftTokenIsExceptional ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component s).1) :
-- imply
  canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component (canonicalStableRawComponentExceptionalSuccessorDirect ends m j k l zero hloop hjk hkl hk0 p hno component s hexceptional) = canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentExceptionalSuccessorDirect_natural ends m j k l zero hloop hjk hkl hk0 p hno component s hexceptional

/--
[canonicalStableRawComponentExceptionalSuccessorDirect_next_or_sibling_of_direct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentExceptionalSuccessorDirect_next_or_sibling_of_direct_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hexceptional : CanonicalStableRawLeftTokenIsExceptional ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component ⟨direct.1, direct.2.1⟩).1) :
-- imply
  let recovered := canonicalStableRawComponentExceptionalSuccessorDirect ends m j k l zero hloop hjk hkl hk0 p hno component ⟨direct.1, direct.2.1⟩ hexceptional let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno direct.1 recovered.1 = next ∨ (recovered.1.source ≠ next.source ∧ recovered.1.target = next.target) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentExceptionalSuccessorDirect_next_or_sibling_of_direct ends m j k l zero hloop hjk hkl hk0 p hno component direct hexceptional

/--
[canonicalStableRawComponentExceptionalSuccessorDirect_eq_next_of_advancing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentExceptionalSuccessorDirect_eq_next_of_advancing_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hadvancing : CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
-- imply
  let hexceptional := canonicalStableRawComponentSuccessorToken_exceptional_of_advancing ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing (canonicalStableRawComponentExceptionalSuccessorDirect ends m j k l zero hloop hjk hkl hk0 p hno component ⟨self.1, self.2.1⟩ hexceptional).1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno self.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentExceptionalSuccessorDirect_eq_next_of_advancing ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing

/--
[canonicalStableRawComponentExceptionalSuccessorDirect_rank_lt_of_advancing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentExceptionalSuccessorDirect_rank_lt_of_advancing_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hadvancing : CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
-- imply
  let hexceptional := canonicalStableRawComponentSuccessorToken_exceptional_of_advancing ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing canonicalStableRawSourceRank ends m j k l zero p (canonicalStableRawComponentExceptionalSuccessorDirect ends m j k l zero hloop hjk hkl hk0 p hno component ⟨self.1, self.2.1⟩ hexceptional).1.source < canonicalStableRawSourceRank ends m j k l zero p self.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentExceptionalSuccessorDirect_rank_lt_of_advancing ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing

/--
[canonicalStableRawComponentForestStep_direct_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentForestStep_direct_split_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨direct.1, direct.2.1⟩ = Sum.inr terminal) ∨ ∃ continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨direct.1, direct.2.1⟩ = Sum.inl continuation ∧ let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno direct.1 continuation.1 = next ∨ (continuation.1.source ≠ next.source ∧ continuation.1.target = next.target) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentForestStep_direct_split ends m j k l zero hloop hjk hkl hk0 p hno component direct

/--
[canonicalStableRawComponentForestStep_direct_next_or_sibling_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentForestStep_direct_next_or_sibling_of_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {direct continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstep : canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨direct.1, direct.2.1⟩ = Sum.inl continuation) :
-- imply
  let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno direct.1 continuation.1 = next ∨ (continuation.1.source ≠ next.source ∧ continuation.1.target = next.target) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentForestStep_direct_next_or_sibling_of_eq ends m j k l zero hloop hjk hkl hk0 p hno component direct continuation hstep

/--
[canonicalStableRawComponentDirectForestAdvance_eq_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentDirectForestAdvance_eq_of_step_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {direct continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstep : canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨direct.1, direct.2.1⟩ = Sum.inl continuation) :
-- imply
  canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component direct = continuation := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDirectForestAdvance_eq_of_step ends m j k l zero hloop hjk hkl hk0 p hno component direct continuation hstep

/--
[exists_canonicalStableRawComponentDirect_terminal_or_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentDirect_terminal_or_cycle_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component (∃ n ≤ Nat.card Direct, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ = Sum.inr terminal) ∨ ∃ startIndex stopIndex : Nat, startIndex < stopIndex ∧ stopIndex ≤ Nat.card Direct ∧ (advance^[startIndex] start) = (advance^[stopIndex] start) ∧ ∀ n < stopIndex, ∃ continuation : Direct, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ = Sum.inl continuation ∧ let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno (advance^[n] start).1 continuation.1 = next ∨ (continuation.1.source ≠ next.source ∧ continuation.1.target = next.target) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentDirect_terminal_or_cycle ends m j k l zero hloop hjk hkl hk0 p hno component start

/--
[exists_canonicalStableRawComponentDirect_terminal_or_rankDrop_or_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentDirect_terminal_or_rankDrop_or_cycle_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component let rank := fun direct : Direct => canonicalStableRawSourceRank ends m j k l zero p direct.1.source (∃ n ≤ Nat.card Direct, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ = Sum.inr terminal) ∨ (∃ n < Nat.card Direct, ∃ continuation : Direct, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ = Sum.inl continuation ∧ rank continuation < rank (advance^[n] start)) ∨ ∃ startIndex stopIndex : Nat, startIndex < stopIndex ∧ stopIndex ≤ Nat.card Direct ∧ (advance^[startIndex] start) = (advance^[stopIndex] start) ∧ ∀ n < stopIndex, ∃ continuation : Direct, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ = Sum.inl continuation ∧ rank (advance^[n] start) ≤ rank continuation ∧ let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno (advance^[n] start).1 continuation.1 = next ∨ (continuation.1.source ≠ next.source ∧ continuation.1.target = next.target) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentDirect_terminal_or_rankDrop_or_cycle ends m j k l zero hloop hjk hkl hk0 p hno component start

/--
[canonicalStableRawComponentDirectSibling_componentPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentDirectSibling_componentPair_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {next : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsource : continuation.1.source ≠ next.source)
  (htarget : continuation.1.target = next.target) :
-- imply
  Nonempty (Fin 2 ↪ CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDirectSibling_componentPair ends m j k l zero hloop hjk hkl hk0 p hno component continuation next hsource htarget

/--
[canonicalStableRawComponentDistinctDirect_twoTokenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentDistinctDirect_twoTokenEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {first second : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hne : first ≠ second) :
-- imply
  Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDistinctDirect_twoTokenEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component first second hne

/--
[canonicalStableRawComponentDistinctDirect_twoDirectEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentDistinctDirect_twoDirectEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {first second : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hne : first ≠ second) :
-- imply
  Nonempty (Fin 2 ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDistinctDirect_twoDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component first second hne

/--
[canonicalStableRawComponentDirectSibling_twoTokenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentDirectSibling_twoTokenEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {direct continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsibling : continuation.1.source ≠ (canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno direct.1).source ∧ continuation.1.target = (canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno direct.1).target) :
-- imply
  Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDirectSibling_twoTokenEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct continuation hsibling

/--
[canonicalStableRawComponentDirectSibling_twoDirectEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentDirectSibling_twoDirectEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {direct continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsibling : continuation.1.source ≠ (canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno direct.1).source ∧ continuation.1.target = (canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno direct.1).target) :
-- imply
  Nonempty (Fin 2 ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDirectSibling_twoDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct continuation hsibling

/--
[canonicalStableRawComponentDirectNext_twoTokenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentDirectNext_twoTokenEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {direct continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hnext : continuation.1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno direct.1) :
-- imply
  Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDirectNext_twoTokenEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct continuation hnext

/--
[canonicalStableRawComponentDirectNext_twoDirectEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentDirectNext_twoDirectEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {direct continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hnext : continuation.1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno direct.1) :
-- imply
  Nonempty (Fin 2 ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDirectNext_twoDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct continuation hnext

/--
[canonicalStableRawComponentDirectCycle_sibling_or_allNext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentDirectCycle_sibling_or_allNext_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {startIndex stopIndex : Nat}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsteps : ∀ n, startIndex ≤ n -> n < stopIndex -> ∃ continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1, ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).2.1⟩ = Sum.inl continuation ∧ let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1 continuation.1 = next ∨ (continuation.1.source ≠ next.source ∧ continuation.1.target = next.target)) :
-- imply
  (∃ n, startIndex ≤ n ∧ n < stopIndex ∧ ∃ continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1, ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).2.1⟩ = Sum.inl continuation ∧ let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1 continuation.1.source ≠ next.source ∧ continuation.1.target = next.target) ∨ ∀ n, startIndex ≤ n -> n < stopIndex -> ∃ continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1, ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).2.1⟩ = Sum.inl continuation ∧ continuation.1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDirectCycle_sibling_or_allNext ends m j k l zero hloop hjk hkl hk0 p hno component start startIndex stopIndex hsteps

/--
[canonicalStableRawComponentDirectAllNext_stableTokens_or_allAdvancing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentDirectAllNext_stableTokens_or_allAdvancing_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {startIndex stopIndex : Nat}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hallNext : ∀ n, startIndex ≤ n -> n < stopIndex -> ∃ continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1, ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).2.1⟩ = Sum.inl continuation ∧ continuation.1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1) :
-- imply
  (∃ n, startIndex ≤ n ∧ n < stopIndex ∧ ∃ continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1 ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1, ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).2.1⟩ = Sum.inl continuation ∧ continuation.1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1 ∧ Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)) ∨ ∀ n, startIndex ≤ n -> n < stopIndex -> CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDirectAllNext_stableTokens_or_allAdvancing ends m j k l zero hloop hjk hkl hk0 p hno component start startIndex stopIndex hallNext

/--
[canonicalStableRawComponentDirectAllNext_project](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentDirectAllNext_project_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {startIndex stopIndex n : Nat}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hn : n ≤ stopIndex - startIndex)
  (hallNext : ∀ q, startIndex ≤ q -> q < stopIndex -> ∃ continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[q] start).1, ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[q] start).2.1⟩ = Sum.inl continuation ∧ continuation.1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[q] start).1) :
-- imply
  let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno (advance^[startIndex + n] start).1 = (next^[n] (advance^[startIndex] start).1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDirectAllNext_project ends m j k l zero hloop hjk hkl hk0 p hno component start startIndex stopIndex n hn hallNext

/--
[canonicalStableRawComponentDirectAllNext_intervalEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentDirectAllNext_intervalEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {startIndex stopIndex first stop : Nat}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hfirstStop : first < stop)
  (hstopLength : stop ≤ stopIndex - startIndex)
  (hallNext : ∀ n, startIndex ≤ n -> n < stopIndex -> ∃ continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1, ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).2.1⟩ = Sum.inl continuation ∧ continuation.1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1)
  (hdistinct : ∀ a b : Nat, a < b -> b < stop -> ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[a] ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[startIndex] start).1).target ≠ ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[b] ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[startIndex] start).1).target) :
-- imply
  Nonempty (Fin (stop - first) ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDirectAllNext_intervalEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component start startIndex stopIndex first stop hfirstStop hstopLength hallNext hdistinct

/--
[canonicalStableRawClosedNextCycle_of_directCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawClosedNextCycle_of_directCycle_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {startIndex stopIndex : Nat}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hlt : startIndex < stopIndex)
  (hrepeat : ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[startIndex] start) = ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[stopIndex] start))
  (hallNext : ∀ n, startIndex ≤ n -> n < stopIndex -> ∃ continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1, ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).2.1⟩ = Sum.inl continuation ∧ continuation.1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1) :
-- imply
  let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno (next^[stopIndex - startIndex] (advance^[startIndex] start).1) = (advance^[startIndex] start).1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawClosedNextCycle_of_directCycle ends m j k l zero hloop hjk hkl hk0 p hno component start startIndex stopIndex hlt hrepeat hallNext

/--
[canonicalStableRawComponentClosedAllNextCycle_tokenDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentClosedAllNextCycle_tokenDichotomy_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {startIndex stopIndex : Nat}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hlt : startIndex < stopIndex)
  (hrepeat : ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[startIndex] start) = ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[stopIndex] start))
  (hallNext : ∀ n, startIndex ≤ n -> n < stopIndex -> ∃ continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1, ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).2.1⟩ = Sum.inl continuation ∧ continuation.1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1) :
-- imply
  Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno let base := advance^[startIndex] start ∃ first stop : Nat, first < stop ∧ stop ≤ stopIndex - startIndex ∧ (next^[first] base.1) = (next^[stop] base.1) ∧ (∀ a b : Nat, a < b -> b < stop -> (next^[a] base.1).target ≠ (next^[b] base.1).target) ∧ (∀ n : Nat, first ≤ n -> n < stop -> CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno (next^[n] base.1)) ∧ Nonempty (Fin (stop - first) ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentClosedAllNextCycle_tokenDichotomy ends m j k l zero hloop hjk hkl hk0 p hno component start startIndex stopIndex hlt hrepeat hallNext

/--
[canonicalStableRawComponentClosedAllNextCycle_balancedBlockDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentClosedAllNextCycle_balancedBlockDichotomy_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {startIndex stopIndex : Nat}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hlt : startIndex < stopIndex)
  (hrepeat : ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[startIndex] start) = ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[stopIndex] start))
  (hallNext : ∀ n, startIndex ≤ n -> n < stopIndex -> ∃ continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1, ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).2.1⟩ = Sum.inl continuation ∧ continuation.1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] start).1) :
-- imply
  (Nonempty (Fin 2 ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) ∧ Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)) ∨ let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno let base := advance^[startIndex] start ∃ first stop : Nat, first < stop ∧ stop ≤ stopIndex - startIndex ∧ (next^[first] base.1) = (next^[stop] base.1) ∧ (∀ a b : Nat, a < b -> b < stop -> (next^[a] base.1).target ≠ (next^[b] base.1).target) ∧ (∀ n : Nat, first ≤ n -> n < stop -> CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno (next^[n] base.1)) ∧ Nonempty (Fin (stop - first) ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) ∧ Nonempty (Fin (stop - first) ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentClosedAllNextCycle_balancedBlockDichotomy ends m j k l zero hloop hjk hkl hk0 p hno component start startIndex stopIndex hlt hrepeat hallNext

/--
[exists_canonicalStableRawComponentDirect_terminal_or_rankDrop_or_balancedBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentDirect_terminal_or_rankDrop_or_balancedBlock_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Token := CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component let rank := fun direct : Direct => canonicalStableRawSourceRank ends m j k l zero p direct.1.source let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno (∃ n ≤ Nat.card Direct, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ = Sum.inr terminal) ∨ (∃ n < Nat.card Direct, ∃ continuation : Direct, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ = Sum.inl continuation ∧ rank continuation < rank (advance^[n] start)) ∨ (Nonempty (Fin 2 ↪ Direct) ∧ Nonempty (Fin 2 ↪ Token)) ∨ ∃ startIndex stopIndex first stop : Nat, startIndex < stopIndex ∧ stopIndex ≤ Nat.card Direct ∧ (advance^[startIndex] start) = (advance^[stopIndex] start) ∧ (∀ q, startIndex ≤ q -> q < stopIndex -> ∃ continuation : Direct, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[q] start).1, (advance^[q] start).2.1⟩ = Sum.inl continuation ∧ continuation.1 = next (advance^[q] start).1) ∧ let base := advance^[startIndex] start first < stop ∧ stop ≤ stopIndex - startIndex ∧ (next^[first] base.1) = (next^[stop] base.1) ∧ (∀ a b : Nat, a < b -> b < stop -> (next^[a] base.1).target ≠ (next^[b] base.1).target) ∧ (∀ q : Nat, first ≤ q -> q < stop -> CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno (next^[q] base.1)) ∧ Nonempty (Fin (stop - first) ↪ Direct) ∧ Nonempty (Fin (stop - first) ↪ Token) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentDirect_terminal_or_rankDrop_or_balancedBlock ends m j k l zero hloop hjk hkl hk0 p hno component start

/--
[exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Token := CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component (∃ n ≤ Nat.card Direct, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ = Sum.inr terminal) ∨ ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ Direct) ∧ Nonempty (Fin size ↪ Token) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock ends m j k l zero hloop hjk hkl hk0 p hno component start

/--
[exists_canonicalStableRawComponentDirect_minRank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentDirect_minRank_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdirect : Nonempty (CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ∃ start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, ∀ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawSourceRank ends m j k l zero p start.1.source ≤ canonicalStableRawSourceRank ends m j k l zero p direct.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentDirect_minRank ends m j k l zero hloop hjk hkl hk0 p hno component hdirect

/--
[canonicalStableRawStableCollisionTargetChildBlock_capacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawStableCollisionTargetChildBlock_capacity_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {target : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hne : (canonicalStableRawStableCollisionTargetChildBlock ends m j k l zero hloop hjk hkl hk0 p hno component target).Nonempty) :
-- imply
  ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p), sources.card = (canonicalStableRawStableCollisionTargetChildBlock ends m j k l zero hloop hjk hkl hk0 p hno component target).card ∧ (canonicalStableRawStableCollisionTargetChildBlock ends m j k l zero hloop hjk hkl hk0 p hno component target).card ≤ (StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (sources.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawStableCollisionTargetChildBlock_capacity ends m j k l zero hloop hjk hkl hk0 p hno component target hne

/--
[canonicalStableRawAdvancingCollisionSuccessorChildBlock_capacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawAdvancingCollisionSuccessorChildBlock_capacity_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {successor : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hne : (canonicalStableRawAdvancingCollisionSuccessorChildBlock ends m j k l zero hloop hjk hkl hk0 p hno component successor).Nonempty) :
-- imply
  ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p), sources.card = (canonicalStableRawAdvancingCollisionSuccessorChildBlock ends m j k l zero hloop hjk hkl hk0 p hno component successor).card ∧ (canonicalStableRawAdvancingCollisionSuccessorChildBlock ends m j k l zero hloop hjk hkl hk0 p hno component successor).card ≤ (StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (sources.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawAdvancingCollisionSuccessorChildBlock_capacity ends m j k l zero hloop hjk hkl hk0 p hno component successor hne

/--
[canonicalStableRawComponentCollisionChildren_rank_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentCollisionChildren_rank_lt_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {self child : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hchild : child ∈ canonicalStableRawComponentCollisionChildren ends m j k l zero hloop hjk hkl hk0 p hno component self) :
-- imply
  canonicalStableRawComponentSelfRank ends m j k l zero hloop hjk hkl hk0 p hno component child < canonicalStableRawComponentSelfRank ends m j k l zero hloop hjk hkl hk0 p hno component self := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentCollisionChildren_rank_lt ends m j k l zero hloop hjk hkl hk0 p hno component self child hchild

/--
[exists_canonicalStableRawComponentReachesTerminal_of_ownerStable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentReachesTerminal_of_ownerStable_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstable : CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
-- imply
  ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, CanonicalStableRawComponentReachesTerminal ends m j k l zero hloop hjk hkl hk0 p hno component self terminal := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentReachesTerminal_of_ownerStable ends m j k l zero hloop hjk hkl hk0 p hno component self hstable

/--
[exists_canonicalStableRawComponentForestStep_terminal_of_ownerStable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentForestStep_terminal_of_ownerStable_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstable : CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
-- imply
  ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨self.1, self.2.1⟩ = Sum.inr terminal := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentForestStep_terminal_of_ownerStable ends m j k l zero hloop hjk hkl hk0 p hno component self hstable

/--
[exists_canonicalStableRawComponentForestStep_direct_of_advancing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentForestStep_direct_of_advancing_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hadvancing : CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
-- imply
  ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨self.1, self.2.1⟩ = Sum.inl direct := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentForestStep_direct_of_advancing ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing

/--
[canonicalStableRawComponentForestStep_token](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentForestStep_token_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {s : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  (match canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component s with | Sum.inl direct => canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct | Sum.inr terminal => terminal.1) = canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentForestStep_token ends m j k l zero hloop hjk hkl hk0 p hno component s

/--
[canonicalStableRawComponentForestStep_direct_output_or_sibling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentForestStep_direct_output_or_sibling_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {s : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstep : canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component s = Sum.inl direct) :
-- imply
  ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = direct.1.target ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p s.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p s.1 u) ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ (u = direct.1 ∨ u.source ≠ direct.1.source) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentForestStep_direct_output_or_sibling ends m j k l zero hloop hjk hkl hk0 p hno component s direct hstep

/--
[canonicalStableRawComponentReferenceOwnerEmbedding_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceOwnerEmbedding_ne_self_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {source target : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  canonicalStableRawComponentReferenceOwnerEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component source ≠ canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component target := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceOwnerEmbedding_ne_self ends m j k l zero hloop hjk hkl hk0 p hno component source target

/--
[canonicalStableRawComponent_two_mul_self_card_le_token](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_two_mul_self_card_le_token_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  2 * Nat.card (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component) ≤ Nat.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_two_mul_self_card_le_token ends m j k l zero hloop hjk hkl hk0 p hno component

/--
[canonicalStableRawComponentReferenceStepEmbedding_inl_rank_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceStepEmbedding_inl_rank_lt_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstep : canonicalStableRawComponentReferenceStepEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component self = Sum.inl direct) :
-- imply
  canonicalStableRawSourceRank ends m j k l zero p direct.1.source < canonicalStableRawSourceRank ends m j k l zero p self.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceStepEmbedding_inl_rank_lt ends m j k l zero hloop hjk hkl hk0 p hno component self direct hstep

/--
[canonicalStableRawComponentReferenceStepBelowRank_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceStepBelowRank_card_le_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {rankBound : Nat}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  Nat.card (CanonicalStableRawComponentSelfBelowRank ends m j k l zero hloop hjk hkl hk0 p hno component rankBound) ≤ Nat.card (CanonicalStableRawComponentDirectBelowRank ends m j k l zero hloop hjk hkl hk0 p hno component rankBound) + Nat.card (CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceStepBelowRank_card_le ends m j k l zero hloop hjk hkl hk0 p hno component rankBound

/--
[canonicalStableRawComponentCrossCollision_source_eq_direct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentCrossCollision_source_eq_direct_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  collision.1.1.1.source = collision.1.2.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentCrossCollision_source_eq_direct ends m j k l zero hloop hjk hkl hk0 p hno component collision

/--
[canonicalStableRawComponentResidualCollision_ranked_sameTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentResidualCollision_ranked_sameTarget_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  collision.1.1.1.2.1.target = collision.1.2.1.target ∧ canonicalStableRawSourceRank ends m j k l zero p collision.1.1.1.2.1.source < canonicalStableRawSourceRank ends m j k l zero p collision.1.2.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentResidualCollision_ranked_sameTarget ends m j k l zero hloop hjk hkl hk0 p hno component collision

/--
[canonicalStableRawComponentResidualLower_fresh_or_rightCollision](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentResidualLower_fresh_or_rightCollision_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let lower := collision.1.1.1.2 (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨lower.1, lower.2.1⟩ = Sum.inr terminal ∧ ∀ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ≠ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∨ ∃ continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨lower.1, lower.2.1⟩ = Sum.inl continuation ∧ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component continuation = canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component ⟨lower.1, lower.2.1⟩ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentResidualLower_fresh_or_rightCollision ends m j k l zero hloop hjk hkl hk0 p hno component collision

/--
[canonicalStableRawComponentResidualLower_rightCollision](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentResidualLower_rightCollision_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstep : canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨collision.1.1.1.2.1, collision.1.1.1.2.2.1⟩ = Sum.inl continuation) :
-- imply
  ∃ third : CanonicalStableRawComponentSecondAlternateDirectCollision ends m j k l zero hloop hjk hkl hk0 p hno component, third.1.1 = collision.1.1 ∧ third.1.2 = continuation := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentResidualLower_rightCollision ends m j k l zero hloop hjk hkl hk0 p hno component collision continuation hstep

/--
[canonicalStableRawComponentResidualLower_continuation_source_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentResidualLower_continuation_source_split_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstep : canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨collision.1.1.1.2.1, collision.1.1.1.2.2.1⟩ = Sum.inl continuation) :
-- imply
  let lower := collision.1.1.1.2 let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno lower.1 let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) := ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p lower.1.target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p lower.1.target⟩ (next.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p lower.1.source ∧ continuation.1.source = owner) ∨ (next.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p lower.1.source ∧ continuation.1.source = lower.1.source ∧ canonicalStableRawSourceRank ends m j k l zero p continuation.1.source = canonicalStableRawSourceRank ends m j k l zero p lower.1.source) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentResidualLower_continuation_source_split ends m j k l zero hloop hjk hkl hk0 p hno component collision continuation hstep

/--
[exists_canonicalStableRawComponentSecondAlternateFiber_freeTerminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentSecondAlternateFiber_freeTerminal_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hfree : (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor), canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩) :
-- imply
  ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p terminal.1.1 = canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentSecondAlternateFiber_freeTerminal ends m j k l zero hloop hjk hkl hk0 p hno component anchor hfree

/--
[exists_canonicalStableRawComponentPreferredSelfOwnerStable_freeTerminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentPreferredSelfOwnerStable_freeTerminal_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {s : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hpreferredSelf : s.1.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p s.1.target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p s.1.target⟩)
  (hstable : CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno s.1) :
-- imply
  ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p terminal.1.1 = (canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno s.1).target := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentPreferredSelfOwnerStable_freeTerminal ends m j k l zero hloop hjk hkl hk0 p hno component s hpreferredSelf hstable

/--
[canonicalStableRawComponentPreferredDirectStep_inl_next](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentPreferredDirectStep_inl_next_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {direct next : CanonicalStableRawComponentPreferredDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstep : canonicalStableRawComponentPreferredDirectStep ends m j k l zero hloop hjk hkl hk0 p hno component direct = Sum.inl next) :
-- imply
  next.1.1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno direct.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentPreferredDirectStep_inl_next ends m j k l zero hloop hjk hkl hk0 p hno component direct next hstep

/--
[canonicalStableRawComponentPreferredDirectAdvance_eq_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentPreferredDirectAdvance_eq_of_step_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {direct next : CanonicalStableRawComponentPreferredDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstep : canonicalStableRawComponentPreferredDirectStep ends m j k l zero hloop hjk hkl hk0 p hno component direct = Sum.inl next) :
-- imply
  partialForestAdvance (canonicalStableRawComponentPreferredDirectStep ends m j k l zero hloop hjk hkl hk0 p hno component) direct = next := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentPreferredDirectAdvance_eq_of_step ends m j k l zero hloop hjk hkl hk0 p hno component direct next hstep

/--
[canonicalStableRawComponentSecondAlternateFiber_terminal_or_preferredSelfOutput](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentSecondAlternateFiber_terminal_or_preferredSelfOutput_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p terminal.1.1 = canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor) ∨ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 u) ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor), canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSecondAlternateFiber_terminal_or_preferredSelfOutput ends m j k l zero hloop hjk hkl hk0 p hno component anchor

/--
[canonicalStableRawComponentSecondAlternatePreferredSelfOutput_stepSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentSecondAlternatePreferredSelfOutput_stepSplit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hpreferredSelf : (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor), canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩) :
-- imply
  (∃ self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, self.1.target = canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧ canonicalStableRawComponentReferenceStepEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component self = Sum.inr terminal) ∨ (∃ self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, self.1.target = canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧ canonicalStableRawComponentReferenceStepEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component self = Sum.inl direct ∧ canonicalStableRawSourceRank ends m j k l zero p direct.1.source < canonicalStableRawSourceRank ends m j k l zero p self.1.source) ∨ ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, direct.1.target = canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 direct.1 ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 direct.1) ∧ (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor), canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSecondAlternatePreferredSelfOutput_stepSplit ends m j k l zero hloop hjk hkl hk0 p hno component anchor hpreferredSelf

/--
[canonicalStableRawComponentSecondAlternateFreeFiberRepresentativesEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentSecondAlternateFreeFiberRepresentativesEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {A : Finset (StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hfree : ∀ anchor ∈ A, (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor), canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩)
  (htarget : Function.Injective fun anchor : ↑A => canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor.1) :
-- imply
  Nonempty (↑A ↪ CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSecondAlternateFreeFiberRepresentativesEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component A hfree htarget

/--
[canonicalStableRawComponentSecondAlternateFiberMinusOne_directResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentSecondAlternateFiberMinusOne_directResidual_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {member : ↑(canonicalStableRawComponentSecondAlternateFiberMinusOne ends m j k l zero hloop hjk hkl hk0 p hno component anchor)}
  {direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htransport : canonicalStableRawComponentSecondAlternateFiberMinusOneSourceTransport ends m j k l zero hloop hjk hkl hk0 p hno component anchor member = Sum.inl direct) :
-- imply
  ∃ residual : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), residual.1.1 = member.1 ∧ residual.1.2 = direct ∧ residual.1.1.1.2.1.target = residual.1.2.1.target ∧ canonicalStableRawSourceRank ends m j k l zero p residual.1.1.1.2.1.source < canonicalStableRawSourceRank ends m j k l zero p residual.1.2.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSecondAlternateFiberMinusOne_directResidual ends m j k l zero hloop hjk hkl hk0 p hno component anchor member direct htransport

/--
[canonicalStableRawComponentSecondAlternateFiber_erase_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentSecondAlternateFiber_erase_card_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  (canonicalStableRawComponentSecondAlternateFiberMinusOne ends m j k l zero hloop hjk hkl hk0 p hno component anchor).card + 1 = (canonicalStableRawComponentSecondCollisionAlternateFiber ends m j k l zero hloop hjk hkl hk0 p hno component anchor).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSecondAlternateFiber_erase_card ends m j k l zero hloop hjk hkl hk0 p hno component anchor

/--
[canonicalStableRawComponentTokenBlock_add_freshTokenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentTokenBlock_add_freshTokenEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {size : Nat}
  {tokens : Fin size ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component}
  {extra : CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hfresh : ∀ i, extra ≠ tokens i) :
-- imply
  Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentTokenBlock_add_freshTokenEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component size tokens extra hfresh

/--
[canonicalStableRawComponentTokenBlock_add_freshSourceCompanion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentTokenBlock_add_freshSourceCompanion_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {size : Nat}
  {tokens : Fin size ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hfresh : ∀ i, canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component anchor ≠ tokens i) :
-- imply
  Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentTokenBlock_add_freshSourceCompanion ends m j k l zero hloop hjk hkl hk0 p hno component anchor size tokens hfresh

/--
[canonicalStableRawComponentReferenceSource_fresh_from_preferredSelfCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceSource_fresh_from_preferredSelfCycle_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {size : Nat}
  {directs : Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {σ : Equiv.Perm (Fin size)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstep : ∀ i, (directs (σ i)).1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno (directs i).1)
  (hpreferredSelf : ∀ i, (directs i).1.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p (directs i).1.target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p (directs i).1.target⟩) :
-- imply
  ∀ i, canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component anchor ≠ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component (directs i) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceSource_fresh_from_preferredSelfCycle ends m j k l zero hloop hjk hkl hk0 p hno component anchor size directs σ hstep hpreferredSelf

/--
[canonicalStableRawComponentPreferredSelfCycle_strictTokenBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentPreferredSelfCycle_strictTokenBlock_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {size : Nat}
  {directs : Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {σ : Equiv.Perm (Fin size)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstep : ∀ i, (directs (σ i)).1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno (directs i).1)
  (hpreferredSelf : ∀ i, (directs i).1.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p (directs i).1.target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p (directs i).1.target⟩) :
-- imply
  Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentPreferredSelfCycle_strictTokenBlock ends m j k l zero hloop hjk hkl hk0 p hno component anchor size directs σ hstep hpreferredSelf

/--
[exists_canonicalStableRawComponentPreferredDirect_terminal_or_strictTokenBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentPreferredDirect_terminal_or_strictTokenBlock_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {start : CanonicalStableRawComponentPreferredDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let Preferred := CanonicalStableRawComponentPreferredDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Token := CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component let step := canonicalStableRawComponentPreferredDirectStep ends m j k l zero hloop hjk hkl hk0 p hno component let advance := partialForestAdvance step (∃ n ≤ Nat.card Preferred, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, step (advance^[n] start) = Sum.inr terminal) ∨ ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ Direct) ∧ Nonempty (Fin (size + 1) ↪ Token) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentPreferredDirect_terminal_or_strictTokenBlock ends m j k l zero hloop hjk hkl hk0 p hno component anchor start

/--
[exists_canonicalStableRawComponentPreferredDirect_strictTokenBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentPreferredDirect_strictTokenBlock_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {start : CanonicalStableRawComponentPreferredDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Token := CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ Direct) ∧ Nonempty (Fin (size + 1) ↪ Token) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentPreferredDirect_strictTokenBlock ends m j k l zero hloop hjk hkl hk0 p hno component anchor start

/--
[canonicalStableRawComponentDirect_strictTokenBlock_of_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentDirect_strictTokenBlock_of_anchor_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) ∧ Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDirect_strictTokenBlock_of_anchor ends m j k l zero hloop hjk hkl hk0 p hno component anchor start

/--
[exists_canonicalStableRawComponentSecondCollision_strictTokenBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentSecondCollision_strictTokenBlock_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) ∧ Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentSecondCollision_strictTokenBlock ends m j k l zero hloop hjk hkl hk0 p hno component anchor

/--
[canonicalStableRawComponentSourceCompanion_strictBlock_or_residualCollision](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentSourceCompanion_strictBlock_or_residualCollision_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {size : Nat}
  {directs : Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ ∃ residual : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), residual.1.1 = anchor ∧ (∃ i, residual.1.2 = directs i) ∧ ∀ old : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), residual.1.2 ≠ old.1.2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSourceCompanion_strictBlock_or_residualCollision ends m j k l zero hloop hjk hkl hk0 p hno component anchor size directs

/--
[canonicalStableRawComponentSourceCompanion_strictBlock_or_lowerRankEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentSourceCompanion_strictBlock_or_lowerRankEntry_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {size : Nat}
  {directs : Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ ∃ i, anchor.1.2.1.target = (directs i).1.target ∧ canonicalStableRawSourceRank ends m j k l zero p anchor.1.2.1.source < canonicalStableRawSourceRank ends m j k l zero p (directs i).1.source ∧ ∀ old : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), directs i ≠ old.1.2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSourceCompanion_strictBlock_or_lowerRankEntry ends m j k l zero hloop hjk hkl hk0 p hno component anchor size directs

/--
[CanonicalStableRawComponentRichIncidenceBlock.extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma extend_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {token : CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hsource : ∀ i, source ≠ block.sources i)
  (htoken : ∀ q, token ≠ block.tokens q)
  (hincident : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source token) :
-- imply
  ∃ extended : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.extend block source token hsource htoken hincident

/--
[CanonicalStableRawComponentRichIncidenceBlock.pivot_size](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma pivot_size_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {index : Fin block.size}
-- given
  (hsource : ∀ i, source ≠ block.sources i)
  (hincident : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source (block.tokens index.castSucc)) :
-- imply
  (block.pivot source hsource index hincident).size = block.size := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.pivot_size block source hsource index hincident

/--
[CanonicalStableRawComponentRichIncidenceBlock.pivot_displaced_fresh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma pivot_displaced_fresh_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {index : Fin block.size}
-- given
  (hsource : ∀ i, source ≠ block.sources i)
  (hincident : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source (block.tokens index.castSucc)) :
-- imply
  ∀ other, block.sources index ≠ (block.pivot source hsource index hincident).sources other := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.pivot_displaced_fresh block source hsource index hincident

/--
[CanonicalStableRawComponentRichIncidenceBlock.closed_or_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma closed_or_crossing_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component} :
-- imply
  block.IsClosed ∨ ∃ source token, CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧ (∀ i, source ≠ block.sources i) ∧ ∃ i, token = block.tokenPrefix i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.closed_or_crossing block

/--
[CanonicalStableRawComponentRichIncidenceBlock.reducedDeficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma reducedDeficit_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hclosed : block.IsClosed)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  Fintype.card (FiniteEmbeddingComplement block.size block.tokenPrefix) < Fintype.card (FiniteEmbeddingComplement block.size block.sources) ∧ ∀ source : FiniteEmbeddingComplement block.size block.sources, ∀ token, CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source.1 token -> token ∉ finiteEmbeddingBlock block.size block.tokenPrefix := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.reducedDeficit block hclosed hdeficit

/--
[exists_canonicalStableRawComponent_closedRichIncidenceBlock_of_extension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_closedRichIncidenceBlock_of_extension_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hextend : ∀ block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, ¬ block.IsClosed -> ∃ extended : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) :
-- imply
  ∃ block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, block.IsClosed := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_closedRichIncidenceBlock_of_extension ends m j k l zero hloop hjk hkl hk0 p hno component start hextend

/--
[exists_canonicalStableRawComponent_sizeMaximalRichIncidenceBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_sizeMaximalRichIncidenceBlock_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  ∃ block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, ∀ other : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, other.size ≤ block.size := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_sizeMaximalRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component start

/--
[CanonicalStableRawComponentRichIncidenceBlock.closureStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma closureStep_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component} :
-- imply
  block.IsClosed ∨ (∃ extended : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) ∨ ∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, (∀ i, source ≠ block.sources i) ∧ ∃ q, canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source = block.tokens q := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.closureStep block

/--
[canonicalStableRawComponent_naturalToken_target_eq_of_direct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_naturalToken_target_eq_of_direct_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hdirect : source.1.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p source.1.source) :
-- imply
  canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source).1 = source.1.target := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_naturalToken_target_eq_of_direct source hdirect

/--
[canonicalStableRawOwnerStableOutput_eq_of_directNaturalTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawOwnerStableOutput_eq_of_directNaturalTarget_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (hdirect : source.1.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p source.1.source)
  (htarget : u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source).1)
  (hstable : CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1 u) :
-- imply
  u = source.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawOwnerStableOutput_eq_of_directNaturalTarget source hdirect u htarget hstable

/--
[canonicalStableRawOwnerAdvancingOutput_false_of_directNaturalTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawOwnerAdvancingOutput_false_of_directNaturalTarget_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (hdirect : source.1.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p source.1.source)
  (htarget : u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source).1)
  (hadvancing : CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p source.1 u) :
-- imply
  False := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawOwnerAdvancingOutput_false_of_directNaturalTarget source hdirect u htarget hadvancing

/--
[CanonicalStableRawComponentRichIncidenceBlock.repeatedNaturalDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma repeatedNaturalDischarge_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {q : Fin (block.size + 1)}
-- given
  (hsource : ∀ i, source ≠ block.sources i)
  (hrepeat : canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source = block.tokens q) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 = canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source) ∨ (∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source).1 ∧ CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source).1 ∧ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.repeatedNaturalDischarge block source hsource q hrepeat

/--
[CanonicalStableRawComponentRichIncidenceBlock.closureDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma closureDischarge_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component} :
-- imply
  block.IsClosed ∨ (∃ extended : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) ∨ (∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 = canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source) ∨ (∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source).1 ∧ CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨ ∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source).1 ∧ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.closureDischarge block

/--
[CanonicalStableRawComponentRichIncidenceBlock.extendBySuccessor_or_repeat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma extendBySuccessor_or_repeat_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hsource : ∀ i, source ≠ block.sources i) :
-- imply
  (∃ extended : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) ∨ ∃ q, canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component source = block.tokens q := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.extendBySuccessor_or_repeat block source hsource

/--
[CanonicalStableRawComponentRichIncidenceBlock.repeatedSuccessorDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma repeatedSuccessorDischarge_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {q : Fin (block.size + 1)}
-- given
  (hsource : ∀ i, source ≠ block.sources i)
  (hrepeat : canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component source = block.tokens q) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 = canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component source) ∨ (∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component source).1 ∧ CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component source).1 ∧ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.repeatedSuccessorDischarge block source hsource q hrepeat

/--
[CanonicalStableRawComponentRichStrictBlock.closed_or_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma closed_or_crossing_eq_2
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component} :
-- imply
  block.IsClosed ∨ ∃ source token, CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧ (∀ i, source ≠ block.sourceBlock i) ∧ ∃ i, token = block.tokenPrefix i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichStrictBlock.closed_or_crossing block

/--
[CanonicalStableRawComponentRichStrictBlock.reducedDeficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma reducedDeficit_eq_2
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hclosed : block.IsClosed)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  Fintype.card (FiniteEmbeddingComplement block.size block.tokenPrefix) < Fintype.card (FiniteEmbeddingComplement block.size block.sourceBlock) ∧ (∃ extra : FiniteEmbeddingComplement block.size block.tokenPrefix, extra.1 = block.tokens (Fin.last block.size)) ∧ ∀ source : FiniteEmbeddingComplement block.size block.sourceBlock, ∀ token, CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source.1 token -> token ∉ finiteEmbeddingBlock block.size block.tokenPrefix := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichStrictBlock.reducedDeficit block hclosed hdeficit

/--
[CanonicalStableRawComponentRichStrictBlock.crossingClassification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma crossingClassification_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {token : CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component}
  {index : Fin block.size}
-- given
  (hincident : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source token)
  (hsource : ∀ i, source ≠ block.sourceBlock i)
  (htoken : token = block.tokenPrefix index) :
-- imply
  (∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p token.1 ∧ CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p token.1 ∧ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichStrictBlock.crossingClassification block source token hincident hsource index htoken

/--
[canonicalStableRawComponent_state_terminal_or_crossCollision_or_direct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_state_terminal_or_crossCollision_or_direct_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {state : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 = canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component state) ∨ (∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), state.1 = collision.1.1.1) ∨ ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, state.1 = direct.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_state_terminal_or_crossCollision_or_direct ends m j k l zero hloop hjk hkl hk0 p hno component state

/--
[CanonicalStableRawComponentRichIncidenceBlock.closureStep_stateClassification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma closureStep_stateClassification_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component} :
-- imply
  block.IsClosed ∨ (∃ extended : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) ∨ ∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, (∀ i, source ≠ block.sources i) ∧ (∃ q, canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source = block.tokens q) ∧ ((∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 = canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source) ∨ (∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), source.1 = collision.1.1.1) ∨ ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, source.1 = direct.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.closureStep_stateClassification block

/--
[canonicalStableRawComponentDirectBlock_add_terminalRichStrictBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentDirectBlock_add_terminalRichStrictBlock_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {size : Nat}
  {directs : Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsize : 0 < size) :
-- imply
  Nonempty (CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDirectBlock_add_terminalRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component size hsize directs terminal

/--
[CanonicalStableRawComponentRichStrictBlock.extendDirect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma extendDirect_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hfresh : ∀ q, canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct ≠ block.tokens q) :
-- imply
  ∃ extended : CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichStrictBlock.extendDirect block direct hfresh

/--
[CanonicalStableRawComponentRichStrictBlock.extendDirect_of_freshSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma extendDirect_of_freshSource_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hsource : ∀ i, source ≠ block.sourceBlock i)
  (hstate : source.1 = direct.1) :
-- imply
  ∃ extended : CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichStrictBlock.extendDirect_of_freshSource block source hsource direct hstate

/--
[exists_canonicalStableRawComponent_closedRichStrictBlock_of_extension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_closedRichStrictBlock_of_extension_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hextend : ∀ block : CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component, ¬ block.IsClosed -> ∃ extended : CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) :
-- imply
  ∃ block : CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component, block.IsClosed := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_closedRichStrictBlock_of_extension ends m j k l zero hloop hjk hkl hk0 p hno component start hextend

/--
[CanonicalStableRawComponentRichStrictBlock.closureStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma closureStep_eq_2
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component} :
-- imply
  block.IsClosed ∨ (∃ extended : CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) ∨ (∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 = canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source) ∨ ∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), source.1 = collision.1.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichStrictBlock.closureStep block

/--
[canonicalStableRawComponentDirectBlock_add_terminalTokenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentDirectBlock_add_terminalTokenEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {size : Nat}
  {directs : Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDirectBlock_add_terminalTokenEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component size directs terminal

/--
[exists_canonicalStableRawComponentDirect_terminal_or_strictTokenBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentDirect_terminal_or_strictTokenBlock_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {available : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Token := CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component (∃ n ≤ Nat.card Direct, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ = Sum.inr terminal) ∨ ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ Direct) ∧ Nonempty (Fin (size + 1) ↪ Token) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentDirect_terminal_or_strictTokenBlock ends m j k l zero hloop hjk hkl hk0 p hno component start available

/--
[exists_canonicalStableRawComponentDirect_strictTokenBlock_of_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentDirect_strictTokenBlock_of_available_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {available : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) ∧ Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentDirect_strictTokenBlock_of_available ends m j k l zero hloop hjk hkl hk0 p hno component start available

/--
[exists_canonicalStableRawComponentDirect_richStrictBlock_of_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentDirect_richStrictBlock_of_available_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {available : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  Nonempty (CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentDirect_richStrictBlock_of_available ends m j k l zero hloop hjk hkl hk0 p hno component start available

/--
[exists_canonicalStableRawComponentDirect_terminal_or_sourceStrictBlock_or_lowerRankEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentDirect_terminal_or_sourceStrictBlock_or_lowerRankEntry_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Token := CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component (∃ n ≤ Nat.card Direct, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ = Sum.inr terminal) ∨ ∃ size : Nat, 0 < size ∧ ∃ directs : Fin size ↪ Direct, Nonempty (Fin (size + 1) ↪ Token) ∨ ∃ i, anchor.1.2.1.target = (directs i).1.target ∧ canonicalStableRawSourceRank ends m j k l zero p anchor.1.2.1.source < canonicalStableRawSourceRank ends m j k l zero p (directs i).1.source ∧ ∀ old : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), directs i ≠ old.1.2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentDirect_terminal_or_sourceStrictBlock_or_lowerRankEntry ends m j k l zero hloop hjk hkl hk0 p hno component anchor start

/--
[canonicalStableRawComponentSecondAlternatePreferredSelfOutput_orbitDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentSecondAlternatePreferredSelfOutput_orbitDischarge_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hpreferredSelf : (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor), canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩) :
-- imply
  (exists self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, self.1.target = canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧ canonicalStableRawComponentReferenceStepEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component self = Sum.inr terminal) ∨ (exists self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, self.1.target = canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧ canonicalStableRawComponentReferenceStepEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component self = Sum.inl direct ∧ canonicalStableRawSourceRank ends m j k l zero p direct.1.source < canonicalStableRawSourceRank ends m j k l zero p self.1.source) ∨ ∃ start : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, start.1.target = canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 start.1 ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 start.1) ∧ (let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Token := CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component (∃ n ≤ Nat.card Direct, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] start).1, (advance^[n] start).2.1⟩ = Sum.inr terminal) ∨ ∃ size : Nat, 0 < size ∧ ∃ directs : Fin size ↪ Direct, Nonempty (Fin (size + 1) ↪ Token) ∨ ∃ i, anchor.1.2.1.target = (directs i).1.target ∧ canonicalStableRawSourceRank ends m j k l zero p anchor.1.2.1.source < canonicalStableRawSourceRank ends m j k l zero p (directs i).1.source ∧ ∀ old : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), directs i ≠ old.1.2) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSecondAlternatePreferredSelfOutput_orbitDischarge ends m j k l zero hloop hjk hkl hk0 p hno component anchor hpreferredSelf

/--
[canonicalStableRawComponentSecondAlternatePreferredSelfOutput_strictDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentSecondAlternatePreferredSelfOutput_strictDischarge_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hpreferredSelf : (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor), canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩) :
-- imply
  (exists self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, self.1.target = canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧ canonicalStableRawComponentReferenceStepEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component self = Sum.inr terminal) ∨ (exists self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, self.1.target = canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧ canonicalStableRawComponentReferenceStepEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component self = Sum.inl direct ∧ canonicalStableRawSourceRank ends m j k l zero p direct.1.source < canonicalStableRawSourceRank ends m j k l zero p self.1.source) ∨ ∃ start : CanonicalStableRawComponentPreferredDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, start.1.1.target = canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 start.1.1 ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p anchor.1.2.1 start.1.1) ∧ (let Preferred := CanonicalStableRawComponentPreferredDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Token := CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component let step := canonicalStableRawComponentPreferredDirectStep ends m j k l zero hloop hjk hkl hk0 p hno component let advance := partialForestAdvance step (∃ n ≤ Nat.card Preferred, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, step (advance^[n] start) = Sum.inr terminal) ∨ ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ Direct) ∧ Nonempty (Fin (size + 1) ↪ Token)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSecondAlternatePreferredSelfOutput_strictDischarge ends m j k l zero hloop hjk hkl hk0 p hno component anchor hpreferredSelf

/--
[exists_canonicalStableRawComponentResidualLower_terminal_or_strictTokenBlock_of_freeFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentResidualLower_terminal_or_strictTokenBlock_of_freeFiber_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {residual : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hfree : (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor), canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondAlternateTarget ends m j k l zero hloop hjk hkl hk0 p hno component anchor)⟩) :
-- imply
  let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Token := CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component let lower : Direct := residual.1.1.1.2 (∃ n ≤ Nat.card Direct, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] lower).1, (advance^[n] lower).2.1⟩ = Sum.inr terminal) ∨ ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ Direct) ∧ Nonempty (Fin (size + 1) ↪ Token) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentResidualLower_terminal_or_strictTokenBlock_of_freeFiber ends m j k l zero hloop hjk hkl hk0 p hno component anchor residual hfree

/--
[exists_canonicalStableRawComponentResidualCollision_of_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentResidualCollision_of_deficit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  Nonempty (StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentResidualCollision_of_deficit ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit

/--
[exists_canonicalStableRawComponentResidualLower_fresh_or_rightCollision_of_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentResidualLower_fresh_or_rightCollision_of_deficit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), collision.1.1.1.2.1.target = collision.1.2.1.target ∧ canonicalStableRawSourceRank ends m j k l zero p collision.1.1.1.2.1.source < canonicalStableRawSourceRank ends m j k l zero p collision.1.2.1.source ∧ (let lower := collision.1.1.1.2 (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨lower.1, lower.2.1⟩ = Sum.inr terminal ∧ ∀ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ≠ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∨ ∃ continuation : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨lower.1, lower.2.1⟩ = Sum.inl continuation ∧ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component continuation = canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component ⟨lower.1, lower.2.1⟩) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentResidualLower_fresh_or_rightCollision_of_deficit ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit

/--
[exists_canonicalStableRawComponent_minRankResidualCollision_of_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_minRankResidualCollision_of_deficit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), ∀ other : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), canonicalStableRawSourceRank ends m j k l zero p collision.1.2.1.source ≤ canonicalStableRawSourceRank ends m j k l zero p other.1.2.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_minRankResidualCollision_of_deficit ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit

/--
[canonicalStableRawComponentResidualDirectPair_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentResidualDirectPair_card_le_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {A : Finset (StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  2 * A.card ≤ Nat.card (CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentResidualDirectPair_card_le ends m j k l zero hloop hjk hkl hk0 p hno component A

/--
[exists_canonicalStableRawComponentResidualOrbitDischarge_of_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentResidualOrbitDischarge_of_deficit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Token := CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component let rank := fun direct : Direct => canonicalStableRawSourceRank ends m j k l zero p direct.1.source ∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), collision.1.1.1.2.1.target = collision.1.2.1.target ∧ rank collision.1.1.1.2 < rank collision.1.2 ∧ ((∃ n ≤ Nat.card Direct, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] collision.1.2).1, (advance^[n] collision.1.2).2.1⟩ = Sum.inr terminal) ∨ (∃ n < Nat.card Direct, ∃ continuation : Direct, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] collision.1.2).1, (advance^[n] collision.1.2).2.1⟩ = Sum.inl continuation ∧ rank continuation < rank (advance^[n] collision.1.2)) ∨ ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ Direct) ∧ Nonempty (Fin size ↪ Token)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentResidualOrbitDischarge_of_deficit ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit

/--
[exists_canonicalStableRawComponentResidual_terminal_or_balancedBlock_of_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentResidual_terminal_or_balancedBlock_of_deficit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Token := CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component ∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), collision.1.1.1.2.1.target = collision.1.2.1.target ∧ canonicalStableRawSourceRank ends m j k l zero p collision.1.1.1.2.1.source < canonicalStableRawSourceRank ends m j k l zero p collision.1.2.1.source ∧ ((∃ n ≤ Nat.card Direct, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] collision.1.2).1, (advance^[n] collision.1.2).2.1⟩ = Sum.inr terminal) ∨ ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ Direct) ∧ Nonempty (Fin size ↪ Token)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentResidual_terminal_or_balancedBlock_of_deficit ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit

/--
[exists_canonicalStableRawComponent_terminalFresh_or_reducedDeficit_of_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_terminalFresh_or_reducedDeficit_of_deficit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  let Self := CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Token := CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component ∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), collision.1.1.1.2.1.target = collision.1.2.1.target ∧ canonicalStableRawSourceRank ends m j k l zero p collision.1.1.1.2.1.source < canonicalStableRawSourceRank ends m j k l zero p collision.1.2.1.source ∧ ((∃ n ≤ Nat.card Direct, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] collision.1.2).1, (advance^[n] collision.1.2).2.1⟩ = Sum.inr terminal ∧ ∀ direct : Direct, terminal.1 ≠ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∨ ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ Direct) ∧ Nonempty (Fin size ↪ Token) ∧ Nat.card Token - size < Nat.card Self + (Nat.card Direct - size)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_terminalFresh_or_reducedDeficit_of_deficit ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit

/--
[canonicalStableRawComponent_minResidual_terminal_or_balancedBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_minResidual_terminal_or_balancedBlock_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hminimal : ∀ other : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), canonicalStableRawSourceRank ends m j k l zero p collision.1.2.1.source ≤ canonicalStableRawSourceRank ends m j k l zero p other.1.2.1.source)
  (horbitBound : ∀ n, canonicalStableRawSourceRank ends m j k l zero p ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] collision.1.2).1.source ≤ canonicalStableRawSourceRank ends m j k l zero p collision.1.2.1.source)
  (hresidual : ∀ n continuation, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] collision.1.2).1, ((canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component)^[n] collision.1.2).2.1⟩ = Sum.inl continuation -> ∃ other : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), other.1.2 = continuation) :
-- imply
  let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Token := CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component (∃ n ≤ Nat.card Direct, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] collision.1.2).1, (advance^[n] collision.1.2).2.1⟩ = Sum.inr terminal) ∨ ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ Direct) ∧ Nonempty (Fin size ↪ Token) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_minResidual_terminal_or_balancedBlock ends m j k l zero hloop hjk hkl hk0 p hno component collision hminimal horbitBound hresidual

/--
[canonicalStableRawComponentReferenceChildren_rank_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceChildren_rank_lt_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {self child : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hchild : child ∈ canonicalStableRawComponentReferenceChildren ends m j k l zero hloop hjk hkl hk0 p hno component self) :
-- imply
  canonicalStableRawComponentSelfRank ends m j k l zero hloop hjk hkl hk0 p hno component child < canonicalStableRawComponentSelfRank ends m j k l zero hloop hjk hkl hk0 p hno component self := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceChildren_rank_lt ends m j k l zero hloop hjk hkl hk0 p hno component self child hchild

/--
[canonicalStableRawComponentReferenceTerminal_mem_of_step_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceTerminal_mem_of_step_inr_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstep : canonicalStableRawComponentReferenceStepEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component self = Sum.inr terminal) :
-- imply
  terminal ∈ canonicalStableRawComponentReferenceTerminalClosure ends m j k l zero hloop hjk hkl hk0 p hno component self := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceTerminal_mem_of_step_inr ends m j k l zero hloop hjk hkl hk0 p hno component self terminal hstep

/--
[canonicalStableRawComponentReferenceChild_terminalClosure_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceChild_terminalClosure_subset_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {self child : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hchild : child ∈ canonicalStableRawComponentReferenceChildren ends m j k l zero hloop hjk hkl hk0 p hno component self) :
-- imply
  canonicalStableRawComponentReferenceTerminalClosure ends m j k l zero hloop hjk hkl hk0 p hno component child ⊆ canonicalStableRawComponentReferenceTerminalClosure ends m j k l zero hloop hjk hkl hk0 p hno component self := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceChild_terminalClosure_subset ends m j k l zero hloop hjk hkl hk0 p hno component self child hchild

/--
[canonicalStableRawTokenComponent_embedding_of_forestStepInjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawTokenComponent_embedding_of_forestStepInjective_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hinjective : Function.Injective (canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  Nonempty (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawTokenComponent_embedding_of_forestStepInjective ends m j k l zero hloop hjk hkl hk0 p hno component hinjective

/--
[canonicalStableRawComponent_cardLE_iff_self_le_nonexceptional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_cardLE_iff_self_le_nonexceptional_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component) ≤ Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) ↔ Nat.card (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component) ≤ Nat.card (CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_cardLE_iff_self_le_nonexceptional ends m j k l zero hloop hjk hkl hk0 p hno component

/--
[canonicalStableRawTokenComponent_embedding_of_direct_card_le_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawTokenComponent_embedding_of_direct_card_le_self_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdirectSelf : Nat.card (CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) ≤ Nat.card (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  Nonempty (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawTokenComponent_embedding_of_direct_card_le_self ends m j k l zero hloop hjk hkl hk0 p hno component hdirectSelf

/--
[canonicalStableRawComponent_direct_card_gt_self_of_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_direct_card_gt_self_of_deficit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  Nat.card (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component) < Nat.card (CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_direct_card_gt_self_of_deficit ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit

/--
[canonicalStableRawTokenComponent_embedding_of_selfNonexceptionalEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawTokenComponent_embedding_of_selfNonexceptionalEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {forest : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component ↪ CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  Nonempty (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawTokenComponent_embedding_of_selfNonexceptionalEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component forest

/--
[canonicalStableRawTokenComponent_embedding_of_terminalClosureHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawTokenComponent_embedding_of_terminalClosureHall_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hhall : ∀ sources : Finset (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component), sources.card ≤ (canonicalStableRawComponentTerminalNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card) :
-- imply
  Nonempty (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawTokenComponent_embedding_of_terminalClosureHall ends m j k l zero hloop hjk hkl hk0 p hno component hhall

/--
[canonicalStableRawTokenComponent_embedding_of_referenceTerminalHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawTokenComponent_embedding_of_referenceTerminalHall_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hhall : ∀ sources : Finset (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component), sources.card ≤ (canonicalStableRawComponentReferenceTerminalNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card) :
-- imply
  Nonempty (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawTokenComponent_embedding_of_referenceTerminalHall ends m j k l zero hloop hjk hkl hk0 p hno component hhall

/--
[canonicalStableRawComponentIncidentNeighborhood_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentIncidentNeighborhood_mono_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  Monotone (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentIncidentNeighborhood_mono ends m j k l zero hloop hjk hkl hk0 p hno component

/--
[canonicalStableRawComponent_tightProperHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_tightProperHall_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) :
-- imply
  ∀ family : Finset ↑sources, family ⊂ Finset.univ -> family.card ≤ (canonicalStableRawComponentRestrictedIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources family).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_tightProperHall ends m j k l zero hloop hjk hkl hk0 p hno component sources hproper

/--
[exists_canonicalStableRawComponent_minimalIncidentObstruction_of_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_minimalIncidentObstruction_of_deficit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ∃ sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), sources.Nonempty ∧ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card ∧ (∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∧ ∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_minimalIncidentObstruction_of_deficit ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit

/--
[exists_other_mem_of_incident_of_delete_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_other_mem_of_incident_of_delete_invariant_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {token : CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsource : source ∈ sources)
  (herase : canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  (hincident : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source token) :
-- imply
  ∃ other ∈ sources, other ≠ source ∧ CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component other token := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_other_mem_of_incident_of_delete_invariant ends m j k l zero hloop hjk hkl hk0 p hno component sources source hsource herase token hincident

/--
[exists_canonicalStableRawComponent_deleteMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_deleteMatching_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsource : source ∈ sources)
  (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) :
-- imply
  ∃ matching : ↑(sources.erase source) ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component, ∀ remaining, CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component remaining.1 (matching remaining) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_deleteMatching ends m j k l zero hloop hjk hkl hk0 p hno component sources source hsource hproper

/--
[exists_canonicalStableRawComponent_tightHoleState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_tightHoleState_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsource : source ∈ sources)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card)
  (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) :
-- imply
  let TightState := ↑sources let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) let incident : TightState -> TightToken -> Prop := fun state token => CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1 ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident, state.hole.1 = source ∧ state.matching.support = Finset.univ.erase state.hole := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_tightHoleState ends m j k l zero hloop hjk hkl hk0 p hno component sources source hsource htight hproper

/--
[exists_canonicalStableRawComponent_saturatedTightHoleState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_saturatedTightHoleState_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsource : source ∈ sources)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card)
  (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) :
-- imply
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) let incident : ↑sources -> TightToken -> Prop := fun state token => CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1 ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident, state.hole.1 = source ∧ ∀ token : TightToken, ∃ matched, state.matching.toFun matched = some token := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_saturatedTightHoleState ends m j k l zero hloop hjk hkl hk0 p hno component sources source hsource htight hproper

/--
[exists_canonicalStableRawComponent_fourSourceEmbedding_of_threeTightTokens](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_fourSourceEmbedding_of_threeTightTokens_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsource : source ∈ sources)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card)
  (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card)
  (hthree : Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources))) :
-- imply
  Nonempty (Fin 4 ↪ ↑sources) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_fourSourceEmbedding_of_threeTightTokens ends m j k l zero hloop hjk hkl hk0 p hno component sources source hsource htight hproper hthree

/--
[canonicalStableRawComponentTightNaturalToken_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentTightNaturalToken_incident_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {state : ↑sources}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component state.1 (canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources state).1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentTightNaturalToken_incident ends m j k l zero hloop hjk hkl hk0 p hno component sources state

/--
[canonicalStableRawComponentTightSuccessorToken_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentTightSuccessorToken_incident_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {state : ↑sources}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component state.1 (canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources state).1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentTightSuccessorToken_incident ends m j k l zero hloop hjk hkl hk0 p hno component sources state

/--
[canonicalStableRawComponent_directOutput_mem_tightNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_directOutput_mem_tightNeighborhood_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {state : ↑sources}
  {token : ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)}
  {u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hincident : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1)
  (huTarget : u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p token.1.1)
  (huKind : CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p state.1.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p state.1.1 u)
  (huComponent : canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component)
  (huDirect : u.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p u.source) :
-- imply
  let direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_directOutput_mem_tightNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources state token hincident u huTarget huKind huComponent huDirect

/--
[canonicalStableRawComponentTightSuccessorEdge_direct_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentTightSuccessorEdge_direct_incident_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {s t : ↑sources}
  {direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (ht : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component t.1 (canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources s).1)
  (hstep : canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component s.1 = Sum.inl direct) :
-- imply
  CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component t.1 (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentTightSuccessorEdge_direct_incident ends m j k l zero hloop hjk hkl hk0 p hno component sources s t ht direct hstep

/--
[canonicalStableRawComponentTightSuccessorEdge_terminal_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentTightSuccessorEdge_terminal_incident_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {s t : ↑sources}
  {terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (ht : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component t.1 (canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources s).1)
  (hstep : canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component s.1 = Sum.inr terminal) :
-- imply
  CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component t.1 terminal.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentTightSuccessorEdge_terminal_incident ends m j k l zero hloop hjk hkl hk0 p hno component sources s t ht terminal hstep

/--
[canonicalStableRawComponentTightSuccessorOther_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentTightSuccessorOther_ne_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {state : ↑sources}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  canonicalStableRawComponentTightSuccessorOther ends m j k l zero hloop hjk hkl hk0 p hno component sources herase state ≠ state := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentTightSuccessorOther_ne ends m j k l zero hloop hjk hkl hk0 p hno component sources herase state

/--
[canonicalStableRawComponentTightSuccessorOther_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentTightSuccessorOther_incident_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {state : ↑sources}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component (canonicalStableRawComponentTightSuccessorOther ends m j k l zero hloop hjk hkl hk0 p hno component sources herase state).1 (canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources state).1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentTightSuccessorOther_incident ends m j k l zero hloop hjk hkl hk0 p hno component sources herase state

/--
[canonicalStableRawComponentTightSuccessorOther_forestStep_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentTightSuccessorOther_forestStep_incident_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {state : ↑sources}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  let next := canonicalStableRawComponentTightSuccessorOther ends m j k l zero hloop hjk hkl hk0 p hno component sources herase (∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component state.1 = Sum.inl direct ∧ CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component (next state).1 (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct)) ∨ ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component state.1 = Sum.inr terminal ∧ CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component (next state).1 terminal.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentTightSuccessorOther_forestStep_incident ends m j k l zero hloop hjk hkl hk0 p hno component sources herase state

/--
[exists_canonicalStableRawComponentTightSuccessorOther_repeat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentTightSuccessorOther_repeat_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hnonempty : sources.Nonempty)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  let next := canonicalStableRawComponentTightSuccessorOther ends m j k l zero hloop hjk hkl hk0 p hno component sources herase ∃ start : ↑sources, ∃ a b : Nat, a < b ∧ b ≤ Fintype.card ↑sources ∧ next^[a] start = next^[b] start ∧ ∀ state, next state ≠ state := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentTightSuccessorOther_repeat ends m j k l zero hloop hjk hkl hk0 p hno component sources hnonempty herase

/--
[exists_canonicalStableRawComponentTightSuccessorOther_localized_repeat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentTightSuccessorOther_localized_repeat_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hnonempty : sources.Nonempty)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  let next := canonicalStableRawComponentTightSuccessorOther ends m j k l zero hloop hjk hkl hk0 p hno component sources herase ∃ start : ↑sources, ∃ a b : Nat, a < b ∧ b ≤ Fintype.card ↑sources ∧ next^[a] start = next^[b] start ∧ (∀ state, next state ≠ state) ∧ ∀ state, (∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component state.1 = Sum.inl direct ∧ CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component (next state).1 (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct)) ∨ ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component state.1 = Sum.inr terminal ∧ CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component (next state).1 terminal.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentTightSuccessorOther_localized_repeat ends m j k l zero hloop hjk hkl hk0 p hno component sources hnonempty herase

/--
[exists_canonicalStableRawComponentTightSuccessorOther_rankNondrop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentTightSuccessorOther_rankNondrop_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hnonempty : sources.Nonempty)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  let next := canonicalStableRawComponentTightSuccessorOther ends m j k l zero hloop hjk hkl hk0 p hno component sources herase ∃ state : ↑sources, ¬ canonicalStableRawSourceRank ends m j k l zero p (next state).1.1.source < canonicalStableRawSourceRank ends m j k l zero p state.1.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentTightSuccessorOther_rankNondrop ends m j k l zero hloop hjk hkl hk0 p hno component sources hnonempty herase

/--
[exists_canonicalStableRawComponent_minimalTightRankNondrop_of_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_minimalTightRankNondrop_of_deficit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ∃ sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), ∃ herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources, sources.Nonempty ∧ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card ∧ (∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) ∧ let next := canonicalStableRawComponentTightSuccessorOther ends m j k l zero hloop hjk hkl hk0 p hno component sources herase ∃ state : ↑sources, ¬ canonicalStableRawSourceRank ends m j k l zero p (next state).1.1.source < canonicalStableRawSourceRank ends m j k l zero p state.1.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_minimalTightRankNondrop_of_deficit ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit

/--
[exists_canonicalStableRawComponent_tightSuccessorOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_tightSuccessorOrbit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsource : source ∈ sources)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card)
  (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) :
-- imply
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) let incident : ↑sources -> TightToken -> Prop := fun state token => CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1 let successor := canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident, ∃ next : ↑sources -> ↑sources, state.hole.1 = source ∧ (∀ s, state.matching.toFun (next s) = some (successor s)) ∧ (∀ s, incident (next s) (successor s)) ∧ (∀ s, next s ≠ state.hole) ∧ ∃ i j : Nat, i < j ∧ j ≤ Fintype.card ↑sources ∧ next^[i] (next state.hole) = next^[j] (next state.hole) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_tightSuccessorOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources source hsource htight hproper

/--
[exists_canonicalStableRawComponent_tightSuccessorCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_tightSuccessorCycle_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsource : source ∈ sources)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card)
  (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) :
-- imply
  let TightState := ↑sources let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) let incident : TightState -> TightToken -> Prop := fun state token => CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1 let successor := canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources ∃ size : Nat, 0 < size ∧ ∃ cycle : Fin size ↪ TightState, ∃ σ : Equiv.Perm (Fin size), ∃ tokens : Fin size ↪ TightToken, ∃ missing : TightState, (∀ i, cycle i ≠ missing) ∧ (∀ i, tokens i = successor (cycle i)) ∧ (∀ i, incident (cycle (σ i)) (tokens i)) ∧ ∃ external : TightState, (∀ q, external ≠ cycle q) ∧ ∃ i, incident external (tokens i) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_tightSuccessorCycle ends m j k l zero hloop hjk hkl hk0 p hno component sources source hsource htight hproper

/--
[canonicalStableRawComponentTightSuccessorEdge_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentTightSuccessorEdge_classification_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {s t : ↑sources}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hne : s.1 ≠ t.1)
  (ht : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component t.1 (canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources s).1) :
-- imply
  ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources s).1 ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p s.1.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p s.1.1 u) ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentTightSuccessorEdge_classification ends m j k l zero hloop hjk hkl hk0 p hno component sources s t hne ht

/--
[exists_canonicalStableRawComponent_tightSuccessorBoundaryOutput](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_tightSuccessorBoundaryOutput_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsource : source ∈ sources)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card)
  (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) :
-- imply
  ∃ size : Nat, 0 < size ∧ ∃ cycle : Fin size ↪ ↑sources, ∃ index : Fin size, ∃ external : ↑sources, (∀ q, external ≠ cycle q) ∧ CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component external.1 (canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources (cycle index)).1 ∧ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources (cycle index)).1 ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p (cycle index).1.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p (cycle index).1.1 u) ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_tightSuccessorBoundaryOutput ends m j k l zero hloop hjk hkl hk0 p hno component sources source hsource htight hproper

/--
[exists_canonicalStableRawComponent_tightSuccessorCycle_terminal_or_directBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_tightSuccessorCycle_terminal_or_directBlock_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsource : source ∈ sources)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card)
  (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ ∃ size : Nat, 0 < size ∧ ∃ directs : Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ tokens : Fin size ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources), ∀ i, canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component (directs i) = (tokens i).1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_tightSuccessorCycle_terminal_or_directBlock ends m j k l zero hloop hjk hkl hk0 p hno component sources source hsource htight hproper

/--
[exists_canonicalStableRawComponent_tightSuccessorBoundary_direct_or_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_tightSuccessorBoundary_direct_or_self_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsource : source ∈ sources)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card)
  (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) :
-- imply
  Nonempty (CanonicalStableRawComponentTightDirectState ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ Nonempty (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_tightSuccessorBoundary_direct_or_self ends m j k l zero hloop hjk hkl hk0 p hno component sources source hsource htight hproper

/--
[exists_canonicalStableRawComponent_tightSuccessorCycle_externalDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_tightSuccessorCycle_externalDischarge_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsource : source ∈ sources)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card)
  (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ ∃ size : Nat, 0 < size ∧ ∃ cycle : Fin size ↪ ↑sources, ∃ directs : Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ tokens : Fin size ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources), ∃ external : ↑sources, (∀ q, external ≠ cycle q) ∧ (∀ i, canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component (directs i) = (tokens i).1) ∧ (Nonempty (Fin (size + 1) ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨ (∃ i, external.1.1 = (directs i).1) ∨ ∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), external.1.1 = collision.1.1.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_tightSuccessorCycle_externalDischarge ends m j k l zero hloop hjk hkl hk0 p hno component sources source hsource htight hproper

/--
[exists_canonicalStableRawComponent_tightSuccessorCycle_fresh_or_exhausts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_tightSuccessorCycle_fresh_or_exhausts_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hsource : source ∈ sources)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card)
  (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) :
-- imply
  let TightState := ↑sources let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∃ size : Nat, 0 < size ∧ ∃ cycle : Fin size ↪ TightState, ∃ external : TightState, (∀ q, external ≠ cycle q) ∧ (Nonempty (Fin (size + 1) ↪ TightToken) ∨ ∀ state : TightState, state = external ∨ ∃ i, state = cycle i) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_tightSuccessorCycle_fresh_or_exhausts ends m j k l zero hloop hjk hkl hk0 p hno component sources source hsource htight hproper

/--
[canonicalStableRawComponent_no_fullTightTokenBlock_of_exhaustiveCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_no_fullTightTokenBlock_of_exhaustiveCycle_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {size : Nat}
  {cycle : Fin size ↪ ↑sources}
  {external : ↑sources}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card)
  (hcover : ∀ state : ↑sources, state = external ∨ ∃ i, state = cycle i)
  (htokens : Nonempty (Fin (size + 1) ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources))) :
-- imply
  False := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_no_fullTightTokenBlock_of_exhaustiveCycle ends m j k l zero hloop hjk hkl hk0 p hno component sources htight size cycle external hcover htokens

/--
[canonicalStableRawComponent_referenceOwnerCollision_mem_tightNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_referenceOwnerCollision_mem_tightNeighborhood_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {external : ↑sources}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : external.1.1 = collision.1.1.1) :
-- imply
  canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_referenceOwnerCollision_mem_tightNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources external collision hself

/--
[canonicalStableRawComponent_referenceSourceCollision_mem_tightNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_referenceSourceCollision_mem_tightNeighborhood_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {external : ↑sources}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : external.1.1 = collision.1.1.1) :
-- imply
  canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_referenceSourceCollision_mem_tightNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources external collision hself

/--
[canonicalStableRawComponent_referenceSourceCollision_ne_ownerCollision](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_referenceSourceCollision_ne_ownerCollision_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠ canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_referenceSourceCollision_ne_ownerCollision ends m j k l zero hloop hjk hkl hk0 p hno component collision

/--
[CanonicalStableRawComponentRichIncidenceBlock.extendByReferenceCharges_or_repeats](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma extendByReferenceCharges_or_repeats_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (hsource : ∀ i, source ≠ block.sources i)
  (hself : source.1 = collision.1.1.1) :
-- imply
  (∃ extended : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) ∨ ∃ q r : Fin (block.size + 1), q ≠ r ∧ canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = block.tokens q ∧ canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = block.tokens r := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.extendByReferenceCharges_or_repeats block source hsource collision hself

/--
[CanonicalStableRawComponentRichIncidenceBlock.closureStep_localized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma closureStep_localized_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component} :
-- imply
  block.IsClosed ∨ (∃ extended : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) ∨ (∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, (∀ i, source ≠ block.sources i) ∧ ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 = canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source ∧ ∃ q, canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source = block.tokens q) ∨ (∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, source.1 = direct.1 ∧ (∀ i, source ≠ block.sources i) ∧ ∃ q r : Fin (block.size + 1), q ≠ r ∧ canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source = block.tokens q ∧ canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component source = block.tokens r) ∨ ∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), source.1 = collision.1.1.1 ∧ (∀ i, source ≠ block.sources i) ∧ ∃ q r s : Fin (block.size + 1), r ≠ s ∧ canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source = block.tokens q ∧ canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = block.tokens r ∧ canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = block.tokens s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.closureStep_localized block

/--
[exists_canonicalStableRawComponent_sizeMaximal_closed_or_localized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_sizeMaximal_closed_or_localized_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {start : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  ∃ block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, (∀ other : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, other.size ≤ block.size) ∧ (block.IsClosed ∨ block.HasLocalizedObstruction) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_sizeMaximal_closed_or_localized ends m j k l zero hloop hjk hkl hk0 p hno component start

/--
[CanonicalStableRawComponentRichIncidenceBlock.HasLocalizedObstruction.extension_or_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma extension_or_pivot_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hobstruction : block.HasLocalizedObstruction) :
-- imply
  (∃ extended : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) ∨ ∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, (∀ i, source ≠ block.sources i) ∧ ∃ index : Fin block.size, CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source (block.tokens index.castSucc) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.HasLocalizedObstruction.extension_or_pivot block hobstruction

/--
[CanonicalStableRawComponentRichIncidenceBlock.HasLocalizedObstruction.pivot_of_sizeMaximal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma pivot_of_sizeMaximal_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hmax : ∀ other : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, other.size ≤ block.size)
  (hobstruction : block.HasLocalizedObstruction) :
-- imply
  ∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ hsource : ∀ i, source ≠ block.sources i, ∃ index : Fin block.size, ∃ hincident : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source (block.tokens index.castSucc), (∀ other, block.sources index ≠ (block.pivot source hsource index hincident).sources other) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.HasLocalizedObstruction.pivot_of_sizeMaximal block hmax hobstruction

/--
[CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.exists_step_of_not_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_step_of_not_closed_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {config : block.PivotConfiguration}
-- given
  (hmax : ∀ other : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, other.size ≤ block.size)
  (hnotClosed : ¬ config.toBlock.IsClosed) :
-- imply
  ∃ next : block.PivotConfiguration, config.Step next ∧ next ≠ config := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.exists_step_of_not_closed block hmax config hnotClosed

/--
[CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.Step.outputClassification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma outputClassification_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {current next : block.PivotConfiguration}
-- given
  (hstep : current.Step next) :
-- imply
  ∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ hsource : ∀ i, source ≠ current.1 i, ∃ index : Fin block.size, next.1 = finiteEmbedding_replaceAt current.1 source hsource index ∧ ((∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (block.tokens index.castSucc).1 ∧ CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (block.tokens index.castSucc).1 ∧ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.Step.outputClassification hstep

/--
[CanonicalStableRawComponentRichIncidenceBlock.exists_rankSumMaximalPivotConfiguration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_rankSumMaximalPivotConfiguration_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component} :
-- imply
  ∃ best : block.PivotConfiguration, ∀ other : block.PivotConfiguration, other.rankSum ≤ best.rankSum := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.exists_rankSumMaximalPivotConfiguration block

/--
[CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.Step.enteringRank_le_displaced_of_rankSumMaximal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma enteringRank_le_displaced_of_rankSumMaximal_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {current next : block.PivotConfiguration}
-- given
  (hmax : ∀ other : block.PivotConfiguration, other.rankSum ≤ current.rankSum)
  (hstep : current.Step next) :
-- imply
  ∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ index : Fin block.size, canonicalStableRawSourceRank ends m j k l zero p source.1.source ≤ canonicalStableRawSourceRank ends m j k l zero p (current.1 index).1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.Step.enteringRank_le_displaced_of_rankSumMaximal hmax hstep

/--
[CanonicalStableRawComponentRichIncidenceBlock.closedConfiguration_or_pivotCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma closedConfiguration_or_pivotCycle_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hmax : ∀ other : CanonicalStableRawComponentRichIncidenceBlock ends m j k l zero hloop hjk hkl hk0 p hno component, other.size ≤ block.size) :
-- imply
  (∃ config : block.PivotConfiguration, config.toBlock.IsClosed) ∨ ∃ size : Nat, 1 < size ∧ ∃ cycle : Fin size ↪ block.PivotConfiguration, ∃ σ : Equiv.Perm (Fin size), ∀ i, (cycle i).Step (cycle (σ i)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentRichIncidenceBlock.closedConfiguration_or_pivotCycle block hmax

/--
[canonicalStableRawComponent_referenceOwner_eq_selfOwnerReroute_of_sourceNormalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_referenceOwner_eq_selfOwnerReroute_of_sourceNormalized_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {state : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : state.1 = collision.1.1.1)
  (hnormalized : canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component state) :
-- imply
  (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision).1 = canonicalStableRawSelfOwnerRerouteLeftToken ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 collision.1.1.2.2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_referenceOwner_eq_selfOwnerReroute_of_sourceNormalized ends m j k l zero hloop hjk hkl hk0 p hno component state collision hself hnormalized

/--
[canonicalStableRawComponent_referenceOwner_eq_successor_of_sourceNormalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_referenceOwner_eq_successor_of_sourceNormalized_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {state : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : state.1 = collision.1.1.1)
  (hnormalized : canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component state) :
-- imply
  canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component state := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_referenceOwner_eq_successor_of_sourceNormalized ends m j k l zero hloop hjk hkl hk0 p hno component state collision hself hnormalized

/--
[canonicalStableRawComponent_sourceNormalized_terminal_or_advancing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_sourceNormalized_terminal_or_advancing_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {external : ↑sources}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : external.1.1 = collision.1.1.1)
  (hnormalized : canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component external.1) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_sourceNormalized_terminal_or_advancing ends m j k l zero hloop hjk hkl hk0 p hno component sources external collision hself hnormalized

/--
[canonicalStableRawComponentTightSuccessorOther_normalizedAdvancingEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentTightSuccessorOther_normalizedAdvancingEdge_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {state : ↑sources}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  (hself : state.1.1 = collision.1.1.1)
  (hnormalized : canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component state.1)
  (hadvancing : CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1) :
-- imply
  let next := canonicalStableRawComponentTightSuccessorOther ends m j k l zero hloop hjk hkl hk0 p hno component sources herase ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component state.1 = Sum.inl direct ∧ canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct ∧ CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component (next state).1 (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∧ canonicalStableRawSourceRank ends m j k l zero p direct.1.source < canonicalStableRawSourceRank ends m j k l zero p collision.1.1.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentTightSuccessorOther_normalizedAdvancingEdge ends m j k l zero hloop hjk hkl hk0 p hno component sources herase state collision hself hnormalized hadvancing

/--
[canonicalStableRawComponentTightSuccessorOther_normalizedAdvancingSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentTightSuccessorOther_normalizedAdvancingSplit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {state : ↑sources}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  (hself : state.1.1 = collision.1.1.1)
  (hnormalized : canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component state.1)
  (hadvancing : CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1) :
-- imply
  let next := canonicalStableRawComponentTightSuccessorOther ends m j k l zero hloop hjk hkl hk0 p hno component sources herase canonicalStableRawSourceRank ends m j k l zero p (next state).1.1.source < canonicalStableRawSourceRank ends m j k l zero p collision.1.1.1.source ∨ ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p (next state).1.1 direct.1 ∧ Nonempty (StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)) ∧ CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component (next state).1 (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∧ canonicalStableRawSourceRank ends m j k l zero p direct.1.source < canonicalStableRawSourceRank ends m j k l zero p collision.1.1.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentTightSuccessorOther_normalizedAdvancingSplit ends m j k l zero hloop hjk hkl hk0 p hno component sources herase state collision hself hnormalized hadvancing

/--
[canonicalStableRawComponentTightSuccessorOther_secondCharge_of_normalizedAdvancing_rankNondrop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentTightSuccessorOther_secondCharge_of_normalizedAdvancing_rankNondrop_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {state : ↑sources}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  (hself : state.1.1 = collision.1.1.1)
  (hnormalized : canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component state.1)
  (hadvancing : CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1)
  (hnondrop : let next := canonicalStableRawComponentTightSuccessorOther ends m j k l zero hloop hjk hkl hk0 p hno component sources herase ¬ canonicalStableRawSourceRank ends m j k l zero p (next state).1.1.source < canonicalStableRawSourceRank ends m j k l zero p collision.1.1.1.source) :
-- imply
  let next := canonicalStableRawComponentTightSuccessorOther ends m j k l zero hloop hjk hkl hk0 p hno component sources herase ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p (next state).1.1 direct.1 ∧ Nonempty (StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)) ∧ CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component (next state).1 (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∧ canonicalStableRawSourceRank ends m j k l zero p direct.1.source < canonicalStableRawSourceRank ends m j k l zero p collision.1.1.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentTightSuccessorOther_secondCharge_of_normalizedAdvancing_rankNondrop ends m j k l zero hloop hjk hkl hk0 p hno component sources herase state collision hself hnormalized hadvancing hnondrop

/--
[canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {state : ↑sources}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ (∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), state.1.1 = collision.1.1.1 ∧ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, state.1.1 = direct.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct ends m j k l zero hloop hjk hkl hk0 p hno component sources state

/--
[canonicalStableRawComponent_tightCrossCollision_localDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_tightCrossCollision_localDischarge_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {state : ↑sources}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  (hself : state.1.1 = collision.1.1.1) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨ ∃ second : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_tightCrossCollision_localDischarge ends m j k l zero hloop hjk hkl hk0 p hno component sources herase state collision hself

/--
[canonicalStableRawComponent_distinctTightStates_localDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_distinctTightStates_localDischarge_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {x y : ↑sources}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  (hne : x ≠ y) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨ (∃ second : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ ∃ first second : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, first ≠ second ∧ x.1.1 = first.1 ∧ y.1.1 = second.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_distinctTightStates_localDischarge ends m j k l zero hloop hjk hkl hk0 p hno component sources herase x y hne

/--
[exists_canonicalStableRawComponent_tightSuccessorCycle_localDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_tightSuccessorCycle_localDischarge_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  (hsource : source ∈ sources)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card)
  (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ ∃ size : Nat, 0 < size ∧ ∃ cycle : Fin size ↪ ↑sources, ∃ directs : Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ tokens : Fin size ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources), ∃ external : ↑sources, (∀ q, external ≠ cycle q) ∧ (∀ i, canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component (directs i) = (tokens i).1) ∧ (Nonempty (Fin (size + 1) ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨ (∃ i, external.1.1 = (directs i).1) ∨ (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨ ∃ second : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_tightSuccessorCycle_localDischarge ends m j k l zero hloop hjk hkl hk0 p hno component sources herase source hsource htight hproper

/--
[exists_canonicalStableRawComponent_minimalRankNondropDischarge_of_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_minimalRankNondropDischarge_of_deficit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ∃ sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), ∃ herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources, sources.Nonempty ∧ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card ∧ (∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) ∧ ∃ state : ↑sources, (let next := canonicalStableRawComponentTightSuccessorOther ends m j k l zero hloop hjk hkl hk0 p hno component sources herase ¬ canonicalStableRawSourceRank ends m j k l zero p (next state).1.1.source < canonicalStableRawSourceRank ends m j k l zero p state.1.1.source) ∧ ((∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧ ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) ∧ Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)) ∨ (∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), state.1.1 = collision.1.1.1 ∧ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧ Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∧ (let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Token := CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component (∃ n ≤ Nat.card Direct, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] collision.1.2).1, (advance^[n] collision.1.2).2.1⟩ = Sum.inr terminal) ∨ ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ Direct) ∧ Nonempty (Fin size ↪ Token))) ∨ (∃ second : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧ ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) ∧ Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)) ∨ ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, state.1.1 = direct.1 ∧ (let Direct := CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component let Token := CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component let advance := canonicalStableRawComponentDirectForestAdvance ends m j k l zero hloop hjk hkl hk0 p hno component (∃ n ≤ Nat.card Direct, ∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component ⟨(advance^[n] direct).1, (advance^[n] direct).2.1⟩ = Sum.inr terminal) ∨ ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ Direct) ∧ Nonempty (Fin size ↪ Token))) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_minimalRankNondropDischarge_of_deficit ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit

/--
[canonicalStableRawComponent_tightCrossCollision_twoAlternateTokenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_tightCrossCollision_twoAlternateTokenEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {external : ↑sources}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : external.1.1 = collision.1.1.1) :
-- imply
  Nonempty (Fin 2 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_tightCrossCollision_twoAlternateTokenEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component sources external collision hself

/--
[canonicalStableRawComponent_tightCrossCollision_sourceNormalized_or_threeTokens](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_tightCrossCollision_sourceNormalized_or_threeTokens_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {external : ↑sources}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : external.1.1 = collision.1.1.1) :
-- imply
  canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component external.1 ∨ Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_tightCrossCollision_sourceNormalized_or_threeTokens ends m j k l zero hloop hjk hkl hk0 p hno component sources external collision hself

/--
[canonicalStableRawComponent_tightCrossCollision_terminal_or_advancing_or_threeTokens](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_tightCrossCollision_terminal_or_advancing_or_threeTokens_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {external : ↑sources}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : external.1.1 = collision.1.1.1) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 ∨ Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_tightCrossCollision_terminal_or_advancing_or_threeTokens ends m j k l zero hloop hjk hkl hk0 p hno component sources external collision hself

/--
[canonicalStableRawComponent_tightCrossCollision_terminal_or_strictBlock_or_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_tightCrossCollision_terminal_or_strictBlock_or_second_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {size : Nat}
  {directs : Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {tokens : Fin size ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)}
  {external : ↑sources}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdirect : ∀ i, canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component (directs i) = (tokens i).1)
  (hself : external.1.1 = collision.1.1.1) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ Nonempty (Fin (size + 1) ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨ Nonempty (StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_tightCrossCollision_terminal_or_strictBlock_or_second ends m j k l zero hloop hjk hkl hk0 p hno component sources size directs tokens hdirect external collision hself

/--
[canonicalStableRawComponentTightHoleMoveAcross_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentTightHoleMoveAcross_classification_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {token : ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (state : StatMech.FrontierA.RelationPartialMatching.HoleState (fun (tightState : ↑sources) (tightToken : ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) => CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component tightState.1 tightToken.1))
  (hincident : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component state.hole.1 token.1) :
-- imply
  let moved := state.moveAcross token hincident state.hole.1 ≠ moved.hole.1 ∧ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p token.1 ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u) ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentTightHoleMoveAcross_classification ends m j k l zero hloop hjk hkl hk0 p hno component sources state token hincident

/--
[canonicalStableRawComponentTightHoleMove_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentTightHoleMove_classification_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (state : StatMech.FrontierA.RelationPartialMatching.HoleState (fun (tightState : ↑sources) (tightToken : ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) => CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component tightState.1 tightToken.1)) :
-- imply
  let natural := canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources let hnatural := canonicalStableRawComponentTightNaturalToken_incident ends m j k l zero hloop hjk hkl hk0 p hno component sources let moved := state.move natural hnatural state.hole.1 ≠ moved.hole.1 ∧ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (natural state.hole).1.1 ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p state.hole.1.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p state.hole.1.1 u) ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentTightHoleMove_classification ends m j k l zero hloop hjk hkl hk0 p hno component sources state

/--
[exists_canonicalStableRawTightComponentSuccessorCollision](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawTightComponentSuccessorCollision_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) let incident : ↑sources -> TightToken -> Prop := fun state token => CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1 let successor := canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources let hsuccessor := canonicalStableRawComponentTightSuccessorToken_incident ends m j k l zero hloop hjk hkl hk0 p hno component sources ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident, state.hole.1 ≠ (state.move successor hsuccessor).hole.1 ∧ successor state.hole = successor (state.move successor hsuccessor).hole := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawTightComponentSuccessorCollision ends m j k l zero hloop hjk hkl hk0 p hno component sources htight

/--
[canonicalStableRawComponentForestStep_eq_of_tightSuccessorToken_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentForestStep_eq_of_tightSuccessorToken_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {x y : ↑sources}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hxy : canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources x = canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources y) :
-- imply
  canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component x.1 = canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component y.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentForestStep_eq_of_tightSuccessorToken_eq ends m j k l zero hloop hjk hkl hk0 p hno component sources x y hxy

/--
[canonicalStableRawComponentForestStepMerger_of_alternatingPathRepeat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentForestStepMerger_of_alternatingPathRepeat_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {size : Nat}
  {path : Fin (size + 1) ↪ ↑sources}
  {tokens : Fin size ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)}
  {index : Fin size}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htransition : ∀ i, tokens i = canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources (path i.castSucc))
  (hrepeat : canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources (path (Fin.last size)) = tokens index) :
-- imply
  (path (Fin.last size)).1 ≠ (path index.castSucc).1 ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component (path (Fin.last size)).1 = canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component (path index.castSucc).1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentForestStepMerger_of_alternatingPathRepeat ends m j k l zero hloop hjk hkl hk0 p hno component sources size path tokens htransition index hrepeat

/--
[canonicalStableRawComponentForestStepMerger_localizedOutput](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentForestStepMerger_localizedOutput_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {x y : ↑sources}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hmerge : canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component x.1 = canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component y.1) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component x.1 = Sum.inr terminal ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component y.1 = Sum.inr terminal) ∨ ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component x.1 = Sum.inl direct ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component y.1 = Sum.inl direct := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentForestStepMerger_localizedOutput ends m j k l zero hloop hjk hkl hk0 p hno component sources x y hmerge

/--
[canonicalStableRawComponentForestStepMerger_threeTokens_of_distinctDirect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentForestStepMerger_threeTokens_of_distinctDirect_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {x y : ↑sources}
  {output first second : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hfirstNeSecond : first ≠ second)
  (hfirst : x.1.1 = first.1)
  (hsecond : y.1.1 = second.1)
  (hx : canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component x.1 = Sum.inl output)
  (hy : canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component y.1 = Sum.inl output) :
-- imply
  Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentForestStepMerger_threeTokens_of_distinctDirect ends m j k l zero hloop hjk hkl hk0 p hno component sources x y output first second hfirstNeSecond hfirst hsecond hx hy

/--
[canonicalStableRawComponentForestStepMerger_localDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponentForestStepMerger_localDischarge_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {x y : ↑sources}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  (hne : x ≠ y)
  (hmerge : canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component x.1 = canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component y.1) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨ ∃ second : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentForestStepMerger_localDischarge ends m j k l zero hloop hjk hkl hk0 p hno component sources herase x y hne hmerge

/--
[exists_canonicalStableRawTightComponentForestStepMerger](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawTightComponentForestStepMerger_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  ∃ x y : ↑sources, x.1 ≠ y.1 ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component x.1 = canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component y.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawTightComponentForestStepMerger ends m j k l zero hloop hjk hkl hk0 p hno component sources htight

/--
[exists_canonicalStableRawTightComponent_localDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawTightComponent_localDischarge_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨ ∃ second : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawTightComponent_localDischarge ends m j k l zero hloop hjk hkl hk0 p hno component sources herase htight

/--
[exists_canonicalStableRawComponent_localDischarge_of_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_localDischarge_of_deficit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ∃ sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), sources.Nonempty ∧ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card ∧ (∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∧ (∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) ∧ ((∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨ ∃ second : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_localDischarge_of_deficit ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit

/--
[exists_canonicalStableRawComponent_strictBlock_or_fourTightSources_of_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_strictBlock_or_fourTightSources_of_deficit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  (∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) ∧ Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)) ∨ ∃ sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), Nonempty (Fin 4 ↪ ↑sources) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_strictBlock_or_fourTightSources_of_deficit ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit

/--
[exists_canonicalStableRawTightComponentCrossCollision](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawTightComponentCrossCollision_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) let incident : ↑sources -> TightToken -> Prop := fun state token => CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1 let natural := canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources let hnatural := canonicalStableRawComponentTightNaturalToken_incident ends m j k l zero hloop hjk hkl hk0 p hno component sources ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident, ∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), state.hole.1.1 = collision.1.1.1 ∧ (state.move natural hnatural).hole.1.1 = collision.1.2.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawTightComponentCrossCollision ends m j k l zero hloop hjk hkl hk0 p hno component sources htight

/--
[exists_canonicalStableRawTightComponent_twoAlternateTokenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawTightComponent_twoAlternateTokenEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  Nonempty (Fin 2 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawTightComponent_twoAlternateTokenEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component sources htight

/--
[exists_canonicalStableRawTightComponent_sourceNormalized_or_four_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawTightComponent_sourceNormalized_or_four_le_card_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  (∃ state : ↑sources, ∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), state.1.1 = collision.1.1.1 ∧ canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component state.1) ∨ 4 ≤ sources.card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawTightComponent_sourceNormalized_or_four_le_card ends m j k l zero hloop hjk hkl hk0 p hno component sources htight

/--
[exists_canonicalStableRawTightComponentFirstChargeOccupant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawTightComponentFirstChargeOccupant_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) let incident : ↑sources -> TightToken -> Prop := fun state token => CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1 let natural := canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources let hnatural := canonicalStableRawComponentTightNaturalToken_incident ends m j k l zero hloop hjk hkl hk0 p hno component sources ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident, ∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), ∃ third : ↑sources, state.hole.1.1 = collision.1.1.1 ∧ (state.move natural hnatural).hole.1.1 = collision.1.2.1 ∧ third ≠ state.hole ∧ third ≠ (state.move natural hnatural).hole ∧ CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component third.1 (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision) ∧ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision).1 ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p state.hole.1.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p state.hole.1.1 u) ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawTightComponentFirstChargeOccupant ends m j k l zero hloop hjk hkl hk0 p hno component sources htight

/--
[exists_canonicalStableRawTightComponentFirstChargeCollisionSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawTightComponentFirstChargeCollisionSplit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  (∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct ∧ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ ∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct ∧ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawTightComponentFirstChargeCollisionSplit ends m j k l zero hloop hjk hkl hk0 p hno component sources htight

/--
[exists_canonicalStableRawTightComponent_distinctDirectTokens_or_sourceNormalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawTightComponent_distinctDirectTokens_or_sourceNormalized_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  (∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), ∃ direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, direct ≠ collision.1.2 ∧ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ ∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision = canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 ∧ canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawTightComponent_distinctDirectTokens_or_sourceNormalized ends m j k l zero hloop hjk hkl hk0 p hno component sources htight

/--
[exists_canonicalStableRawTightComponent_threeStateTwoTokenPeelData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawTightComponent_threeStateTwoTokenPeelData_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) let incident : ↑sources -> TightToken -> Prop := fun state token => CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1 let natural := canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources let hnatural := canonicalStableRawComponentTightNaturalToken_incident ends m j k l zero hloop hjk hkl hk0 p hno component sources ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident, ∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), ∃ third : ↑sources, ∃ first : TightToken, state.hole.1.1 = collision.1.1.1 ∧ (state.move natural hnatural).hole.1.1 = collision.1.2.1 ∧ third ≠ state.hole ∧ third ≠ (state.move natural hnatural).hole ∧ state.hole ≠ (state.move natural hnatural).hole ∧ first.1 = canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision ∧ natural state.hole ≠ first ∧ incident state.hole (natural state.hole) ∧ incident (state.move natural hnatural).hole (natural state.hole) ∧ incident state.hole first ∧ incident third first := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawTightComponent_threeStateTwoTokenPeelData ends m j k l zero hloop hjk hkl hk0 p hno component sources htight

/--
[CanonicalStableRawTightChargeOrbit.extendPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma extendPair_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
  {source : ↑sources}
  {token : ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)}
-- given
  (hsource : ∀ i, source ≠ orbit.states i)
  (htoken : ∀ i, token ≠ orbit.tokens i)
  (hincident : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source.1 token.1)
  (horigin : token = canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source ∨ token = canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source) :
-- imply
  ∃ extended : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, extended.size = orbit.size + 1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.extendPair orbit source token hsource htoken hincident horigin

/--
[CanonicalStableRawTightChargeOrbit.sourceSaturated_or_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma sourceSaturated_or_crossing_eq_2
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources} :
-- imply
  orbit.SourceSaturated ∨ ∃ source token, CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source.1 token.1 ∧ (∃ i, source = orbit.states i) ∧ ∀ i, token ≠ orbit.tokens i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.sourceSaturated_or_crossing orbit

/--
[CanonicalStableRawTightChargeOrbit.sourceSaturated_or_external_or_chord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma sourceSaturated_or_external_or_chord_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  orbit.SourceSaturated ∨ (∃ external token, CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component external.1 token.1 ∧ (∀ i, external ≠ orbit.states i) ∧ ∀ i, token ≠ orbit.tokens i) ∨ ∃ q r : Fin (orbit.size + 1), q ≠ r ∧ ∃ token, CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component (orbit.states q).1 token.1 ∧ CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component (orbit.states r).1 token.1 ∧ ∀ s, token ≠ orbit.tokens s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.sourceSaturated_or_external_or_chord orbit herase

/--
[CanonicalStableRawTightChargeOrbit.internalChordClassification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma internalChordClassification_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
  {q r : Fin (orbit.size + 1)}
  {token : ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)}
-- given
  (hqr : q ≠ r)
  (hq : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component (orbit.states q).1 token.1)
  (hr : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component (orbit.states r).1 token.1) :
-- imply
  (∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p token.1.1 ∧ CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p (orbit.states q).1.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p token.1.1 ∧ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p (orbit.states q).1.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.internalChordClassification orbit q r hqr token hq hr

/--
[CanonicalStableRawTightChargeOrbit.SourceSaturated.exhaustive_of_properHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exhaustive_of_properHall_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (hsaturated : orbit.SourceSaturated)
  (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) :
-- imply
  ∀ source : ↑sources, ∃ i, source = orbit.states i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.SourceSaturated.exhaustive_of_properHall orbit hsaturated hproper

/--
[CanonicalStableRawTightChargeOrbit.SourceSaturated.tokens_exhaustive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma tokens_exhaustive_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (hsaturated : orbit.SourceSaturated)
  (hstates : ∀ source : ↑sources, ∃ i, source = orbit.states i) :
-- imply
  ∀ token : ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources), ∃ i, token = orbit.tokens i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.SourceSaturated.tokens_exhaustive orbit hsaturated hstates

/--
[CanonicalStableRawTightChargeOrbit.SourceSaturated.exhaustive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exhaustive_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (hsaturated : orbit.SourceSaturated)
  (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) :
-- imply
  (∀ source : ↑sources, ∃ i, source = orbit.states i) ∧ ∀ token : ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources), ∃ i, token = orbit.tokens i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.SourceSaturated.exhaustive orbit hsaturated hproper

/--
[CanonicalStableRawTightChargeOrbit.SourceSaturated.surplusNaturalDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma surplusNaturalDischarge_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (hsaturated : orbit.SourceSaturated) :
-- imply
  ∃ q, canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources (orbit.states 0) = orbit.tokens q ∧ ((∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources (orbit.states 0)).1.1 ∧ CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p (orbit.states 0).1.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources (orbit.states 0)).1.1 ∧ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p (orbit.states 0).1.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.SourceSaturated.surplusNaturalDischarge orbit hsaturated

/--
[CanonicalStableRawTightChargeOrbit.SourceSaturated.surplusNatural_rankSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma surplusNatural_rankSplit_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (hsaturated : orbit.SourceSaturated) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ (∃ q, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources (orbit.states 0) = orbit.tokens q ∧ u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources (orbit.states 0)).1.1 ∧ CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p (orbit.states 0).1.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p (orbit.states 0).1.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.SourceSaturated.surplusNatural_rankSplit orbit hsaturated

/--
[CanonicalStableRawTightChargeOrbit.tokenSaturated_or_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma tokenSaturated_or_crossing_eq_2
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources} :
-- imply
  orbit.TokenSaturated ∨ ∃ source token, CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source.1 token.1 ∧ (∀ i, source ≠ orbit.states i) ∧ ∃ i, token = orbit.tokens i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.tokenSaturated_or_crossing orbit

/--
[CanonicalStableRawTightChargeOrbit.extendByNatural_or_repeat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma extendByNatural_or_repeat_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
  {source : ↑sources}
-- given
  (hsource : ∀ i, source ≠ orbit.states i) :
-- imply
  (∃ extended : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, extended.size = orbit.size + 1) ∨ ∃ i, canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source = orbit.tokens i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.extendByNatural_or_repeat orbit source hsource

/--
[CanonicalStableRawTightChargeOrbit.extendBySuccessor_or_repeat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma extendBySuccessor_or_repeat_eq_2
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
  {source : ↑sources}
-- given
  (hsource : ∀ i, source ≠ orbit.states i) :
-- imply
  (∃ extended : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, extended.size = orbit.size + 1) ∨ ∃ i, canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source = orbit.tokens i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.extendBySuccessor_or_repeat orbit source hsource

/--
[CanonicalStableRawTightChargeOrbit.repeatedSuccessorDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma repeatedSuccessorDischarge_eq_2
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
  {source : ↑sources}
  {q : Fin orbit.size}
-- given
  (hsource : ∀ i, source ≠ orbit.states i)
  (hrepeat : canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source = orbit.tokens q) :
-- imply
  (∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source).1.1 ∧ CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source).1.1 ∧ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.repeatedSuccessorDischarge orbit source hsource q hrepeat

/--
[CanonicalStableRawTightChargeOrbit.repeatedNaturalDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma repeatedNaturalDischarge_eq_2
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
  {source : ↑sources}
  {q : Fin orbit.size}
-- given
  (hsource : ∀ i, source ≠ orbit.states i)
  (hrepeat : canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source = orbit.tokens q) :
-- imply
  (∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source).1.1 ∧ CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source).1.1 ∧ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.repeatedNaturalDischarge orbit source hsource q hrepeat

/--
[CanonicalStableRawTightChargeOrbit.saturationStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma saturationStep_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources} :
-- imply
  orbit.TokenSaturated ∨ (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ (∃ extended : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, extended.size = orbit.size + 1) ∨ ∃ source : ↑sources, (∀ i, source ≠ orbit.states i) ∧ ∃ q, canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source = orbit.tokens q := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.saturationStep orbit

/--
[CanonicalStableRawTightChargeOrbit.saturationStep_classified](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma saturationStep_classified_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources} :
-- imply
  orbit.TokenSaturated ∨ (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ (∃ extended : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, extended.size = orbit.size + 1) ∨ (∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨ ∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.saturationStep_classified orbit

/--
[CanonicalStableRawTightChargeOrbit.saturationStep_rankSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma saturationStep_rankSplit_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources} :
-- imply
  orbit.TokenSaturated ∨ (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ (∃ extended : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, extended.size = orbit.size + 1) ∨ (∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, (∀ i, source ≠ orbit.states i) ∧ (∃ r, canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source = orbit.tokens r) ∧ u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source).1.1 ∧ CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨ ∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p source.1.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.saturationStep_rankSplit orbit

/--
[CanonicalStableRawTightChargeOrbit.saturationStep_grow_or_rankDrop_or_repeat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma saturationStep_grow_or_rankDrop_or_repeat_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources} :
-- imply
  orbit.TokenSaturated ∨ (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ (∃ extended : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, extended.size = orbit.size + 1) ∨ (∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p source.1.1.source) ∨ orbit.HasStableSuccessorRepeat := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.saturationStep_grow_or_rankDrop_or_repeat orbit

/--
[CanonicalStableRawTightChargeOrbit.HasStableSuccessorRepeat.originSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma originSplit_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (hobstruction : orbit.HasStableSuccessorRepeat) :
-- imply
  (∃ source : ↑sources, ∃ q : Fin orbit.size, (∀ i, source ≠ orbit.states i) ∧ canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source = canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources (orbit.states q.succ)) ∨ (∃ source : ↑sources, ∃ q : Fin orbit.size, source.1 ≠ (orbit.states q.succ).1 ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component source.1 = canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component (orbit.states q.succ).1) ∨ ∃ source : ↑sources, (∀ i, source ≠ orbit.states i) ∧ canonicalStableRawComponentTightSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source = orbit.tokens orbit.coreFirst := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasStableSuccessorRepeat.originSplit hobstruction

/--
[CanonicalStableRawTightChargeOrbit.saturationStep_grow_or_rankDrop_or_merger](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma saturationStep_grow_or_rankDrop_or_merger_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  orbit.TokenSaturated ∨ (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ (∃ extended : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, extended.size = orbit.size + 1) ∨ (∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p source.1.1.source) ∨ ∃ x y : ↑sources, x.1 ≠ y.1 ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component x.1 = canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component y.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.saturationStep_grow_or_rankDrop_or_merger orbit htight

/--
[CanonicalStableRawTightChargeOrbit.saturationStep_localDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma saturationStep_localDischarge_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  orbit.TokenSaturated ∨ (∃ extended : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, extended.size = orbit.size + 1) ∨ (∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p source.1.1.source) ∨ orbit.LocalMergerDischarge := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.saturationStep_localDischarge orbit herase htight

/--
[CanonicalStableRawTightChargeOrbit.sourceSaturationStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma sourceSaturationStep_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component, terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ (∃ extended : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, extended.size = orbit.size + 1) ∨ (∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨ (∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨ ∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p source.1.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.sourceSaturationStep orbit herase

/--
[CanonicalStableRawTightChargeOrbit.bidirectionalSaturationStep_localDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma bidirectionalSaturationStep_localDischarge_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  (∃ extended : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, extended.size = orbit.size + 1) ∨ (∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨ (∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨ (∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p source.1.1.source) ∨ orbit.LocalMergerDischarge := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.bidirectionalSaturationStep_localDischarge orbit herase htight

/--
[exists_canonicalStableRawTightComponent_initialChargeFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawTightComponent_initialChargeFamily_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  let TightState := ↑sources let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) let incident : TightState -> TightToken -> Prop := fun state token => CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1 let natural := canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources let hnatural := canonicalStableRawComponentTightNaturalToken_incident ends m j k l zero hloop hjk hkl hk0 p hno component sources ∃ family : FiniteRelationDeficiencyOneFamily TightState TightToken, ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident, ∃ third : TightState, ∃ first : TightToken, family.states = {state.hole, (state.move natural hnatural).hole, third} ∧ family.tokens = {natural state.hole, first} ∧ incident state.hole (natural state.hole) ∧ incident (state.move natural hnatural).hole (natural state.hole) ∧ incident state.hole first ∧ incident third first := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawTightComponent_initialChargeFamily ends m j k l zero hloop hjk hkl hk0 p hno component sources htight

/--
[exists_canonicalStableRawTightComponent_initialChargeOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawTightComponent_initialChargeOrbit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  ∃ orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, orbit.size = 2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawTightComponent_initialChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources htight

/--
[exists_canonicalStableRawTightComponent_sizeMaximalChargeOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawTightComponent_sizeMaximalChargeOrbit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  ∃ orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, 2 ≤ orbit.size ∧ ∀ other : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, other.size ≤ orbit.size := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawTightComponent_sizeMaximalChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources htight

/--
[CanonicalStableRawTightChargeOrbit.TokenSaturated.exhaustive_of_sizeMaximal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exhaustive_of_sizeMaximal_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (hsaturated : orbit.TokenSaturated)
  (hmax : ∀ other : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, other.size ≤ orbit.size)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  (∀ source : ↑sources, ∃ i, source = orbit.states i) ∧ (∀ token : ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources), ∃ i, token = orbit.tokens i) ∧ orbit.SourceSaturated := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.TokenSaturated.exhaustive_of_sizeMaximal orbit hsaturated hmax htight

/--
[CanonicalStableRawTightChargeOrbit.maximalSaturationStep_localDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma maximalSaturationStep_localDischarge_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (hmax : ∀ other : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, other.size ≤ orbit.size)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  orbit.HasRetainedSharedTokenOutput ∨ orbit.HasFreshInternalChordOutput ∨ (∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p source.1.1.source) ∨ orbit.LocalMergerDischarge := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.maximalSaturationStep_localDischarge orbit hmax herase htight

/--
[CanonicalStableRawTightChargeOrbit.maximalSaturationStep_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma maximalSaturationStep_sharp_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (hmax : ∀ other : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, other.size ≤ orbit.size)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  (htight : (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card) :
-- imply
  orbit.HasRetainedSharedTokenOutput ∨ (∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p source.1.1.source) ∨ orbit.LocalMergerDischarge := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.maximalSaturationStep_sharp orbit hmax herase htight

/--
[canonicalStableRawComponent_squareOutput_tightDirect_or_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_squareOutput_tightDirect_or_self_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {state : ↑sources}
  {token : ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)}
  {u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hincident : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1)
  (htarget : u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p token.1.1)
  (hkind : CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p state.1.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p state.1.1 u)
  (hcomponent : canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component) :
-- imply
  Nonempty (CanonicalStableRawComponentTightDirectState ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ Nonempty (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_squareOutput_tightDirect_or_self ends m j k l zero hloop hjk hkl hk0 p hno component sources state token hincident u htarget hkind hcomponent

/--
[CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.direct_or_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma direct_or_self_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (houtput : orbit.HasRetainedSharedTokenOutput) :
-- imply
  Nonempty (CanonicalStableRawComponentTightDirectState ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ Nonempty (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.direct_or_self houtput

/--
[CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.direct_or_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma direct_or_self_eq_2
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (houtput : orbit.HasFreshInternalChordOutput) :
-- imply
  Nonempty (CanonicalStableRawComponentTightDirectState ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨ Nonempty (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.direct_or_self houtput

/--
[canonicalStableRawComponent_directNaturalSquareOutput_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_directNaturalSquareOutput_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {source : ↑sources}
  {token : ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)}
  {u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hnatural : token = canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source)
  (htarget : u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p token.1.1)
  (hkind : CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p source.1.1 u)
  (hdirect : source.1.1.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p source.1.1.source) :
-- imply
  CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧ u = source.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_directNaturalSquareOutput_eq ends m j k l zero hloop hjk hkl hk0 p hno component sources source token hnatural u htarget hkind hdirect

/--
[canonicalStableRawComponent_directNaturalIncidence_endpointSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_directNaturalIncidence_endpointSplit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {firstState secondState : ↑sources}
  {first second : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {token : ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hfirst : firstState.1.1 = first.1)
  (hsecond : secondState.1.1 = second.1)
  (hnatural : token = canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources firstState)
  (hsecondIncident : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component secondState.1 token.1) :
-- imply
  first.1.source = second.1.source ∨ first.1.source = ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p second.1.target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p second.1.target⟩ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_directNaturalIncidence_endpointSplit ends m j k l zero hloop hjk hkl hk0 p hno component sources firstState secondState first second hfirst hsecond token hnatural hsecondIncident

/--
[canonicalStableRawComponent_directPair_threeTokens_or_firstStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_directPair_threeTokens_or_firstStep_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {firstState secondState : ↑sources}
  {first second : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hne : first ≠ second)
  (hfirst : firstState.1.1 = first.1)
  (hsecond : secondState.1.1 = second.1) :
-- imply
  Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component firstState.1 = Sum.inl second := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_directPair_threeTokens_or_firstStep ends m j k l zero hloop hjk hkl hk0 p hno component sources firstState secondState first second hne hfirst hsecond

/--
[canonicalStableRawComponent_directPair_threeTokens_or_twoCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_directPair_threeTokens_or_twoCycle_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {firstState secondState : ↑sources}
  {first second : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hne : first ≠ second)
  (hfirst : firstState.1.1 = first.1)
  (hsecond : secondState.1.1 = second.1) :
-- imply
  Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨ (canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component firstState.1 = Sum.inl second ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component secondState.1 = Sum.inl first) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_directPair_threeTokens_or_twoCycle ends m j k l zero hloop hjk hkl hk0 p hno component sources firstState secondState first second hne hfirst hsecond

/--
[canonicalStableRawComponent_directPair_threeTokens_or_token_eq_natural](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma canonicalStableRawComponent_directPair_threeTokens_or_token_eq_natural_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {firstState secondState : ↑sources}
  {first second : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {token : ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hne : first ≠ second)
  (hfirst : firstState.1.1 = first.1)
  (hsecond : secondState.1.1 = second.1) :
-- imply
  Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨ token = canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources firstState ∨ token = canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources secondState := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponent_directPair_threeTokens_or_token_eq_natural ends m j k l zero hloop hjk hkl hk0 p hno component sources firstState secondState first second hne hfirst hsecond token

/--
[CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.local_or_directPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma local_or_directPair_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (houtput : orbit.HasRetainedSharedTokenOutput)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  orbit.LocalMergerDischarge ∨ (orbit.HasRetainedSharedTokenOutput ∧ ∃ source : ↑sources, ∃ q : Fin orbit.size, ∃ first second : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, source ≠ orbit.states q.succ ∧ first ≠ second ∧ source.1.1 = first.1 ∧ (orbit.states q.succ).1.1 = second.1 ∧ ∃ token : ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources), ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, token = canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources source ∧ token = orbit.tokens q ∧ u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p token.1.1 ∧ CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∧ u = source.1.1 ∧ (first.1.source = second.1.source ∨ first.1.source = ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p second.1.target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p second.1.target⟩)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.local_or_directPair houtput herase

/--
[CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_directPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma local_or_directPair_eq_2
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (houtput : orbit.HasFreshInternalChordOutput)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  orbit.LocalMergerDischarge ∨ (orbit.HasFreshInternalChordOutput ∧ ∃ q r : Fin (orbit.size + 1), ∃ first second : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, q ≠ r ∧ first ≠ second ∧ (orbit.states q).1.1 = first.1 ∧ (orbit.states r).1.1 = second.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_directPair houtput herase

/--
[CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.local_or_firstDirectStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma local_or_firstDirectStep_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (houtput : orbit.HasRetainedSharedTokenOutput)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  orbit.LocalMergerDischarge ∨ (orbit.HasRetainedSharedTokenOutput ∧ ∃ source : ↑sources, ∃ q : Fin orbit.size, ∃ first second : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, source ≠ orbit.states q.succ ∧ first ≠ second ∧ source.1.1 = first.1 ∧ (orbit.states q.succ).1.1 = second.1 ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component source.1 = Sum.inl second) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.local_or_firstDirectStep houtput herase

/--
[CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_firstDirectStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma local_or_firstDirectStep_eq_2
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (houtput : orbit.HasFreshInternalChordOutput)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  orbit.LocalMergerDischarge ∨ (orbit.HasFreshInternalChordOutput ∧ ∃ q r : Fin (orbit.size + 1), ∃ first second : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, q ≠ r ∧ first ≠ second ∧ (orbit.states q).1.1 = first.1 ∧ (orbit.states r).1.1 = second.1 ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component (orbit.states q).1 = Sum.inl second) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_firstDirectStep houtput herase

/--
[CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.local_or_directTwoCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma local_or_directTwoCycle_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (houtput : orbit.HasRetainedSharedTokenOutput)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  orbit.LocalMergerDischarge ∨ (orbit.HasRetainedSharedTokenOutput ∧ ∃ source : ↑sources, ∃ q : Fin orbit.size, ∃ first second : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, source ≠ orbit.states q.succ ∧ first ≠ second ∧ source.1.1 = first.1 ∧ (orbit.states q.succ).1.1 = second.1 ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component source.1 = Sum.inl second ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component (orbit.states q.succ).1 = Sum.inl first) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.local_or_directTwoCycle houtput herase

/--
[CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_directTwoCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma local_or_directTwoCycle_eq_2
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (houtput : orbit.HasFreshInternalChordOutput)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  orbit.LocalMergerDischarge ∨ (orbit.HasFreshInternalChordOutput ∧ ∃ q r : Fin (orbit.size + 1), ∃ first second : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, q ≠ r ∧ first ≠ second ∧ (orbit.states q).1.1 = first.1 ∧ (orbit.states r).1.1 = second.1 ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component (orbit.states q).1 = Sum.inl second ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component (orbit.states r).1 = Sum.inl first) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_directTwoCycle houtput herase

/--
[CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_naturalTwoCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma local_or_naturalTwoCycle_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (houtput : orbit.HasFreshInternalChordOutput)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  orbit.LocalMergerDischarge ∨ ∃ q r : Fin (orbit.size + 1), ∃ token : ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources), ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, ∃ first second : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component, q ≠ r ∧ first ≠ second ∧ (orbit.states q).1.1 = first.1 ∧ (orbit.states r).1.1 = second.1 ∧ (∀ s, token ≠ orbit.tokens s) ∧ CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component (orbit.states q).1 token.1 ∧ CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component (orbit.states r).1 token.1 ∧ u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p token.1.1 ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p (orbit.states q).1.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p (orbit.states q).1.1 u) ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ (token = canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources (orbit.states q) ∨ token = canonicalStableRawComponentTightNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component sources (orbit.states r)) ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component (orbit.states q).1 = Sum.inl second ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component (orbit.states r).1 = Sum.inl first := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_naturalTwoCycle houtput herase

/--
[CanonicalStableRawComponentBalancedDirectBlock.sourceBlock_tokenBlock_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma sourceBlock_tokenBlock_incident_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {index : Fin block.size} :
-- imply
  CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component (block.sourceBlock index) (block.tokenBlock index) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.sourceBlock_tokenBlock_incident block index

/--
[CanonicalStableRawComponentBalancedDirectBlock.successorToken_fresh_or_retainedOther](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma successorToken_fresh_or_retainedOther_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {index : Fin block.size} :
-- imply
  let successor := canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component (block.sourceBlock index) successor ∉ finiteEmbeddingBlock block.size block.tokenBlock ∨ ∃ next, next ≠ index ∧ successor = block.tokenBlock next := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.successorToken_fresh_or_retainedOther block index

/--
[CanonicalStableRawComponentBalancedDirectBlock.complementNeighborhood_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma complementNeighborhood_mono_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component} :
-- imply
  Monotone block.complementNeighborhood := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.complementNeighborhood_mono block

/--
[CanonicalStableRawTightChargeOrbit.HasDirectOrbitDischarge.richStrictBlock_or_balancedBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma richStrictBlock_or_balancedBlock_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (hdischarge : orbit.HasDirectOrbitDischarge) :
-- imply
  Nonempty (CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ ∃ size : Nat, 0 < size ∧ Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) ∧ Nonempty (Fin size ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasDirectOrbitDischarge.richStrictBlock_or_balancedBlock hdischarge

/--
[CanonicalStableRawTightChargeOrbit.HasDirectOrbitDischarge.richStrict_or_balancedResidual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma richStrict_or_balancedResidual_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component))
  (hdischarge : orbit.HasDirectOrbitDischarge) :
-- imply
  Nonempty (CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ orbit.HasBalancedResidualDeficit := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasDirectOrbitDischarge.richStrict_or_balancedResidual hdeficit hdischarge

/--
[CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit.exists_block](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_block_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (hresidual : orbit.HasBalancedResidualDeficit) :
-- imply
  ∃ block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component, Nat.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) - block.size < Nat.card (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component) + (Nat.card (CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) - block.size) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit.exists_block hresidual

/--
[CanonicalStableRawComponentBalancedDirectBlock.closed_or_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma closed_or_crossing_eq_3
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component} :
-- imply
  block.IsClosed ∨ ∃ source token, CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧ (∀ i, source ≠ block.sourceBlock i) ∧ ∃ i, token = block.tokenBlock i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.closed_or_crossing block

/--
[CanonicalStableRawComponentBalancedDirectBlock.complement_strictDeficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma complement_strictDeficit_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  Fintype.card block.TokenComplement < Fintype.card block.StateComplement := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.complement_strictDeficit block hdeficit

/--
[CanonicalStableRawComponentBalancedDirectBlock.stateComplement_card_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma stateComplement_card_lt_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component} :
-- imply
  Fintype.card block.StateComplement < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.stateComplement_card_lt block

/--
[CanonicalStableRawComponentBalancedDirectBlock.no_componentFiberRealization_of_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma no_componentFiberRealization_of_deficit_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ¬ block.HasComponentFiberRealization := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.no_componentFiberRealization_of_deficit block hdeficit

/--
[CanonicalStableRawComponentBalancedDirectBlock.IsClosed.restricts_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma restricts_incidence_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {source : block.StateComplement}
  {token : CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hclosed : block.IsClosed)
  (hincident : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source.1 token) :
-- imply
  token ∉ finiteEmbeddingBlock block.size block.tokenBlock := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.IsClosed.restricts_incidence hclosed source token hincident

/--
[CanonicalStableRawComponentBalancedDirectBlock.exists_minimalComplementTightFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_minimalComplementTightFamily_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ∃ family : Finset block.StateComplement, family.Nonempty ∧ (block.complementNeighborhood family).card + 1 = family.card ∧ (∀ source ∈ family, block.complementNeighborhood (family.erase source) = block.complementNeighborhood family) ∧ ∀ smaller : Finset block.StateComplement, smaller ⊂ family -> smaller.card ≤ (block.complementNeighborhood smaller).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.exists_minimalComplementTightFamily block hdeficit

/--
[CanonicalStableRawComponentBalancedDirectBlock.exists_smallerComplementMinimalTightProblem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_smallerComplementMinimalTightProblem_eq
  [Fintype I]
  [DecidableEq I]
  {I : Type uI}
  {W : Type uW}
  [Fintype I]
  [DecidableEq I]
  [Fintype W]
  [DecidableEq W]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hclosed : block.IsClosed)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ∃ problem : FiniteRelationMinimalTightProblem.{uI, uI}, problem.rank < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component) ∧ ∀ source : block.StateComplement, ∀ token : CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component, CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source.1 token -> token ∉ finiteEmbeddingBlock block.size block.tokenBlock := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.exists_smallerComplementMinimalTightProblem block hclosed hdeficit

/--
[CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.exists_crossingContinuation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_crossingContinuation_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hcross : block.HasGeometricCrossing) :
-- imply
  ∃ continuation : FiniteRelationCrossingContinuation (CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component), continuation.size = block.size ∧ let move := StatMech.FrontierA.RelationPartialMatching.HoleState.move continuation.natural continuation.natural_incident ∃ start stop : Nat, start < stop ∧ stop ≤ block.size + 1 ∧ (move^[start] continuation.initialHoleState).hole = (move^[stop] continuation.initialHoleState).hole ∧ ∀ a b : Nat, a < b -> b < stop -> (move^[a] continuation.initialHoleState).hole ≠ (move^[b] continuation.initialHoleState).hole := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.exists_crossingContinuation hcross

/--
[CanonicalStableRawComponentBalancedDirectBlock.HasNaturalTokenEscape.augmentedBlock_or_alternate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma augmentedBlock_or_alternate_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hescape : block.HasNaturalTokenEscape) :
-- imply
  block.HasAugmentedIncidentBlock ∨ ∃ source, ∃ index q : Fin block.size, (∀ i, source ≠ block.sourceBlock i) ∧ CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source (block.tokenBlock index) ∧ q ≠ index ∧ canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component source = block.tokenBlock q := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.HasNaturalTokenEscape.augmentedBlock_or_alternate hescape

/--
[CanonicalStableRawComponentBalancedDirectBlock.HasNaturalTokenEscape.augmentedBlock_or_nonreversingContinuation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma augmentedBlock_or_nonreversingContinuation_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hescape : block.HasNaturalTokenEscape) :
-- imply
  block.HasAugmentedIncidentBlock ∨ ∃ continuation : FiniteRelationCrossingContinuation (CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component), continuation.size = block.size ∧ ∃ alternate : continuation.Token, alternate ≠ continuation.index ∧ continuation.incident (Sum.inr ()) alternate ∧ let moved := continuation.initialHoleState.move continuation.natural continuation.natural_incident ∃ hincident' : continuation.incident moved.hole alternate, (moved.moveAcross alternate hincident').hole = Sum.inl alternate := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.HasNaturalTokenEscape.augmentedBlock_or_nonreversingContinuation hescape

/--
[CanonicalStableRawComponentBalancedDirectBlock.HasOldOutputCrossing.naturalEscape_or_stableSelf_or_advancingRankDrop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma naturalEscape_or_stableSelf_or_advancingRankDrop_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hcross : block.HasOldOutputCrossing) :
-- imply
  block.HasNaturalTokenEscape ∨ block.HasStableSelfOldOutput ∨ block.HasAdvancingOldOutputRankDrop := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.HasOldOutputCrossing.naturalEscape_or_stableSelf_or_advancingRankDrop hcross

/--
[CanonicalStableRawComponentBalancedDirectBlock.HasStableSelfOldOutput.terminal_or_rankDrop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma terminal_or_rankDrop_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hstable : block.HasStableSelfOldOutput) :
-- imply
  Nonempty (CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ ∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p source.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.HasStableSelfOldOutput.terminal_or_rankDrop hstable

/--
[CanonicalStableRawComponentBalancedDirectBlock.geometricCrossing_of_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma geometricCrossing_of_crossing_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
  {token : CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component}
  {index : Fin block.size}
-- given
  (hincident : CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source token)
  (hsource : ∀ i, source ≠ block.sourceBlock i)
  (htoken : token = block.tokenBlock index) :
-- imply
  block.HasGeometricCrossing := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.geometricCrossing_of_crossing block source token hincident hsource index htoken

/--
[CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.exists_crossingFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_crossingFamily_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hcross : block.HasGeometricCrossing) :
-- imply
  ∃ source token, ∃ hsource : ∀ i, source ≠ block.sourceBlock i, let family := block.crossingFamily source hsource source ∈ family.states ∧ token ∈ family.tokens ∧ CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p token.1 ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p source.1 u) ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.exists_crossingFamily hcross

/--
[CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.exists_reroutedSourceBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_reroutedSourceBlock_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hcross : block.HasGeometricCrossing) :
-- imply
  ∃ source token, ∃ index : Fin block.size, ∃ hsource : ∀ i, source ≠ block.sourceBlock i, let rerouted := finiteEmbedding_replaceAt block.sourceBlock source hsource index token = block.tokenBlock index ∧ rerouted index = source ∧ (∀ q, q ≠ index -> rerouted q = block.sourceBlock q) ∧ (∀ q, CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component (rerouted q) (block.tokenBlock q)) ∧ block.sourceBlock index ∉ finiteEmbeddingBlock block.size rerouted := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.exists_reroutedSourceBlock hcross

/--
[CanonicalStableRawComponentBalancedDirectBlock.HasOldOutputCrossing.output_displaced_or_retained](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma output_displaced_or_retained_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hcross : block.HasOldOutputCrossing) :
-- imply
  ∃ source token, ∃ index oldIndex : Fin block.size, ∃ hsource : ∀ i, source ≠ block.sourceBlock i, let rerouted := finiteEmbedding_replaceAt block.sourceBlock source hsource index CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧ token = block.tokenBlock index ∧ block.sourceBlock index ∉ finiteEmbeddingBlock block.size rerouted ∧ (oldIndex = index ∨ block.sourceBlock oldIndex ∈ finiteEmbeddingBlock block.size rerouted) ∧ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u = (block.directs oldIndex).1 ∧ u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p token.1 ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p source.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p source.1 u) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.HasOldOutputCrossing.output_displaced_or_retained hcross

/--
[CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_oldOutput](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma growth_or_self_or_oldOutput_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hcross : block.HasGeometricCrossing) :
-- imply
  (∃ extended : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) ∨ Nonempty (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ block.HasOldOutputCrossing := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_oldOutput hcross

/--
[CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_naturalEscape_or_stableSelf_or_rankDrop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma growth_or_self_or_naturalEscape_or_stableSelf_or_rankDrop_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hcross : block.HasGeometricCrossing) :
-- imply
  (∃ extended : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) ∨ Nonempty (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ block.HasNaturalTokenEscape ∨ block.HasStableSelfOldOutput ∨ block.HasAdvancingOldOutputRankDrop := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_naturalEscape_or_stableSelf_or_rankDrop hcross

/--
[CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_naturalEscape_or_terminal_or_rankDrop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma growth_or_self_or_naturalEscape_or_terminal_or_rankDrop_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hcross : block.HasGeometricCrossing) :
-- imply
  (∃ extended : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) ∨ Nonempty (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ block.HasNaturalTokenEscape ∨ Nonempty (CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ ∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p source.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_naturalEscape_or_terminal_or_rankDrop hcross

/--
[CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit.complementTightFamily_or_geometricCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma complementTightFamily_or_geometricCrossing_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (hresidual : orbit.HasBalancedResidualDeficit)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ∃ block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component, (block.IsClosed ∧ Fintype.card block.StateComplement < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component) ∧ Fintype.card block.TokenComplement < Fintype.card block.StateComplement ∧ (∃ family : Finset block.StateComplement, family.Nonempty ∧ (block.complementNeighborhood family).card + 1 = family.card ∧ (∀ source ∈ family, block.complementNeighborhood (family.erase source) = block.complementNeighborhood family) ∧ ∀ smaller : Finset block.StateComplement, smaller ⊂ family -> smaller.card ≤ (block.complementNeighborhood smaller).card) ∧ ∀ source : block.StateComplement, ∀ token, CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source.1 token -> token ∉ finiteEmbeddingBlock block.size block.tokenBlock) ∨ block.HasGeometricCrossing := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit.complementTightFamily_or_geometricCrossing hresidual hdeficit

/--
[CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit.smallerRecursion_or_crossingContinuation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma smallerRecursion_or_crossingContinuation_eq
  [Fintype I]
  [DecidableEq I]
  {I : Type uI}
  {W : Type uW}
  [Fintype I]
  [DecidableEq I]
  [Fintype W]
  [DecidableEq W]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (hresidual : orbit.HasBalancedResidualDeficit)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ∃ block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component, (block.IsClosed ∧ ∃ problem : FiniteRelationMinimalTightProblem.{uI, uI}, problem.rank < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component) ∧ ∀ source : block.StateComplement, ∀ token : CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component, CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source.1 token -> token ∉ finiteEmbeddingBlock block.size block.tokenBlock) ∨ (block.HasGeometricCrossing ∧ ∃ continuation : FiniteRelationCrossingContinuation (CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component), continuation.size = block.size ∧ let move := StatMech.FrontierA.RelationPartialMatching.HoleState.move continuation.natural continuation.natural_incident ∃ start stop : Nat, start < stop ∧ stop ≤ block.size + 1 ∧ (move^[start] continuation.initialHoleState).hole = (move^[stop] continuation.initialHoleState).hole ∧ ∀ a b : Nat, a < b -> b < stop -> (move^[a] continuation.initialHoleState).hole ≠ (move^[b] continuation.initialHoleState).hole) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit.smallerRecursion_or_crossingContinuation hresidual hdeficit

/--
[CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.local_or_directOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma local_or_directOrbit_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (houtput : orbit.HasRetainedSharedTokenOutput)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  orbit.LocalMergerDischarge ∨ orbit.HasDirectOrbitDischarge := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.local_or_directOrbit houtput herase

/--
[CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_directOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma local_or_directOrbit_eq_2
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (houtput : orbit.HasFreshInternalChordOutput)
  (herase : ∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
-- imply
  orbit.LocalMergerDischarge ∨ orbit.HasDirectOrbitDischarge := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_directOrbit houtput herase

/--
[exists_canonicalStableRawComponent_maximalOrbitDischarge_of_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_maximalOrbitDischarge_of_deficit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ∃ sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), sources.Nonempty ∧ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card ∧ (∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∧ (∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) ∧ ∃ orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, 2 ≤ orbit.size ∧ (orbit.HasRetainedSharedTokenOutput ∨ orbit.HasFreshInternalChordOutput ∨ (∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p source.1.1.source) ∨ orbit.LocalMergerDischarge) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_maximalOrbitDischarge_of_deficit ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit

/--
[exists_canonicalStableRawComponent_maximalOrbitSharpDischarge_of_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_maximalOrbitSharpDischarge_of_deficit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ∃ sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), sources.Nonempty ∧ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card ∧ (∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∧ (∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) ∧ ∃ orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, 2 ≤ orbit.size ∧ ((∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p source.1.1.source) ∨ orbit.LocalMergerDischarge ∨ orbit.HasDirectOrbitDischarge) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_maximalOrbitSharpDischarge_of_deficit ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit

/--
[exists_canonicalStableRawComponent_maximalOrbitResidualDischarge_of_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponent_maximalOrbitResidualDischarge_of_deficit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ∃ sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), sources.Nonempty ∧ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 = sources.card ∧ (∀ source ∈ sources, canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (sources.erase source) = canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∧ (∀ smaller : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component), smaller ⊂ sources -> smaller.card ≤ (canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component smaller).card) ∧ ∃ orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources, 2 ≤ orbit.size ∧ ((∃ source : ↑sources, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p source.1.1.source) ∨ orbit.LocalMergerDischarge ∨ Nonempty (CanonicalStableRawComponentRichStrictBlock ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ orbit.HasBalancedResidualDeficit) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponent_maximalOrbitResidualDischarge_of_deficit ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit

/--
[CanonicalStableRawComponentBalancedDirectBlock.directSuccessorStep_eq_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma directSuccessorStep_eq_inl_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {index next : Fin block.size}
-- given
  (hstep : block.directSuccessorStep index = Sum.inl next) :
-- imply
  next ≠ index ∧ canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component (block.sourceBlock index) = block.tokenBlock next := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.directSuccessorStep_eq_inl block index next hstep

/--
[CanonicalStableRawComponentBalancedDirectBlock.directSuccessorStep_eq_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma directSuccessorStep_eq_inr_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {index : Fin block.size}
  {token : CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hstep : block.directSuccessorStep index = Sum.inr token) :
-- imply
  token = canonicalStableRawComponentSuccessorToken ends m j k l zero hloop hjk hkl hk0 p hno component (block.sourceBlock index) ∧ token ∉ finiteEmbeddingBlock block.size block.tokenBlock := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.directSuccessorStep_eq_inr block index token hstep

/--
[CanonicalStableRawComponentBalancedDirectBlock.exists_postSecond_terminal_or_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_postSecond_terminal_or_cycle_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {entrance : Fin block.size} :
-- imply
  (∃ n ≤ block.size + 1, ∃ token, block.postSecondStep entrance ((partialForestAdvance (block.postSecondStep entrance))^[n] (Sum.inl ())) = Sum.inr token ∧ token ∉ finiteEmbeddingBlock block.size block.tokenBlock) ∨ ∃ i j : Nat, i < j ∧ j ≤ block.size + 1 ∧ ((partialForestAdvance (block.postSecondStep entrance))^[i] (Sum.inl ())) = ((partialForestAdvance (block.postSecondStep entrance))^[j] (Sum.inl ())) ∧ (∀ n < j, ∃ next, block.postSecondStep entrance ((partialForestAdvance (block.postSecondStep entrance))^[n] (Sum.inl ())) = Sum.inl next) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.exists_postSecond_terminal_or_cycle block entrance

/--
[partialForestNonbacktrackingStep_eq_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma partialForestNonbacktrackingStep_eq_inl_eq
  [Fintype I]
  [DecidableEq I]
  {step : A → A ⊕ B}
  {state next : PartialForestNonbacktrackingState A}
-- given
  (hloopFree : ∀ current next, step current = Sum.inl next → next ≠ current)
  (hstep : partialForestNonbacktrackingStep step hloopFree state = Sum.inl next) :
-- imply
  next.1.1 = state.1.2 ∧ next.1.2 ≠ state.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.partialForestNonbacktrackingStep_eq_inl step hloopFree state next hstep

/--
[partialForestNonbacktrackingStep_eq_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma partialForestNonbacktrackingStep_eq_terminal_eq
  [Fintype I]
  [DecidableEq I]
  {step : A → A ⊕ B}
  {state : PartialForestNonbacktrackingState A}
  {terminal : B}
-- given
  (hloopFree : ∀ current next, step current = Sum.inl next → next ≠ current)
  (hstep : partialForestNonbacktrackingStep step hloopFree state = Sum.inr (Sum.inl terminal)) :
-- imply
  step state.1.2 = Sum.inr terminal := by
-- proof
  apply StatMech.GrahamGHS.FourColor.partialForestNonbacktrackingStep_eq_terminal step hloopFree state terminal hstep

/--
[partialForestNonbacktrackingStep_eq_backtrack](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma partialForestNonbacktrackingStep_eq_backtrack_eq
  [Fintype I]
  [DecidableEq I]
  {step : A → A ⊕ B}
  {state : PartialForestNonbacktrackingState A}
-- given
  (hloopFree : ∀ current next, step current = Sum.inl next → next ≠ current)
  (hstep : partialForestNonbacktrackingStep step hloopFree state = Sum.inr (Sum.inr ())) :
-- imply
  step state.1.2 = Sum.inl state.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.partialForestNonbacktrackingStep_eq_backtrack step hloopFree state hstep

/--
[exists_partialForest_terminal_or_backtrack_or_longCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_partialForest_terminal_or_backtrack_or_longCycle_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  [DecidableEq A]
  {step : A → A ⊕ B}
  {start : PartialForestNonbacktrackingState A}
-- given
  (hloopFree : ∀ current next, step current = Sum.inl next → next ≠ current) :
-- imply
  ( ∃ n ≤ Fintype.card (PartialForestNonbacktrackingState A), ∃ terminal, step (((partialForestAdvance (partialForestNonbacktrackingStep step hloopFree))^[n] start).1.2) = Sum.inr terminal) ∨ ( ∃ n ≤ Fintype.card (PartialForestNonbacktrackingState A), step (((partialForestAdvance (partialForestNonbacktrackingStep step hloopFree))^[n] start).1.2) = Sum.inl (((partialForestAdvance (partialForestNonbacktrackingStep step hloopFree))^[n] start).1.1)) ∨ ∃ i j : Nat, i + 3 ≤ j ∧ j ≤ Fintype.card (PartialForestNonbacktrackingState A) ∧ ((partialForestAdvance (partialForestNonbacktrackingStep step hloopFree))^[i] start) = ((partialForestAdvance (partialForestNonbacktrackingStep step hloopFree))^[j] start) ∧ ∀ n < j, ∃ next, partialForestNonbacktrackingStep step hloopFree ((partialForestAdvance (partialForestNonbacktrackingStep step hloopFree))^[n] start) = Sum.inl next := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_partialForest_terminal_or_backtrack_or_longCycle step hloopFree start

/--
[CanonicalStableRawComponentBalancedDirectBlock.postSecondStep_continuation_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma postSecondStep_continuation_ne_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {entrance : Fin block.size}
  {state next : block.PostSecondState}
-- given
  (hstep : block.postSecondStep entrance state = Sum.inl next) :
-- imply
  next ≠ state := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.postSecondStep_continuation_ne block entrance state next hstep

/--
[CanonicalStableRawComponentBalancedDirectBlock.postSecondStep_terminal_fresh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma postSecondStep_terminal_fresh_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {entrance : Fin block.size}
  {state : block.PostSecondState}
  {token : CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hstep : block.postSecondStep entrance state = Sum.inr token) :
-- imply
  token ∉ finiteEmbeddingBlock block.size block.tokenBlock := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.postSecondStep_terminal_fresh block entrance state token hstep

/--
[CanonicalStableRawComponentBalancedDirectBlock.exists_postSecond_terminal_or_backtrack_or_longCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_postSecond_terminal_or_backtrack_or_longCycle_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I → Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {entrance : Fin block.size} :
-- imply
  let lifted := block.postSecondContinuationStep entrance let advance := partialForestAdvance lifted let start := block.postSecondInitialState entrance ( ∃ n ≤ Fintype.card block.PostSecondContinuationState, ∃ token, block.postSecondStep entrance (advance^[n] start).1.2 = Sum.inr token ∧ token ∉ finiteEmbeddingBlock block.size block.tokenBlock) ∨ ( ∃ n ≤ Fintype.card block.PostSecondContinuationState, block.postSecondStep entrance (advance^[n] start).1.2 = Sum.inl (advance^[n] start).1.1) ∨ ∃ i j : Nat, i + 3 ≤ j ∧ j ≤ Fintype.card block.PostSecondContinuationState ∧ advance^[i] start = advance^[j] start ∧ ∀ n < j, ∃ next, lifted (advance^[n] start) = Sum.inl next := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.exists_postSecond_terminal_or_backtrack_or_longCycle block entrance

/--
[CanonicalStableRawComponentBalancedDirectBlock.postSecondStep_terminal_growth_or_nonexceptional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma postSecondStep_terminal_growth_or_nonexceptional_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {entrance : Fin block.size}
  {state : block.PostSecondState}
  {token : CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hstep : block.postSecondStep entrance state = Sum.inr token) :
-- imply
  (∃ extended : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) ∨ Nonempty (CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.postSecondStep_terminal_growth_or_nonexceptional block entrance state token hstep

/--
[CanonicalStableRawComponentBalancedDirectBlock.postSecond_growth_or_nonexceptional_or_backtrack_or_longCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma postSecond_growth_or_nonexceptional_or_backtrack_or_longCycle_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {entrance : Fin block.size} :
-- imply
  (∃ extended : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) ∨ Nonempty (CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ block.HasPostSecondBacktrack entrance ∨ block.HasPostSecondLongCycle entrance := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.postSecond_growth_or_nonexceptional_or_backtrack_or_longCycle block entrance

/--
[CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_augmented_or_postSecond_or_terminal_or_rankDrop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma growth_or_self_or_augmented_or_postSecond_or_terminal_or_rankDrop_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hcross : block.HasGeometricCrossing) :
-- imply
  (∃ extended : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) ∨ Nonempty (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ block.HasAugmentedIncidentBlock ∨ (∃ entrance, block.HasPostSecondBacktrack entrance) ∨ (∃ entrance, block.HasPostSecondLongCycle entrance) ∨ Nonempty (CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ ∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p source.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_augmented_or_postSecond_or_terminal_or_rankDrop hcross

/--
[partialForestNonbacktrackingStep_eq_inl_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma partialForestNonbacktrackingStep_eq_inl_relation_eq
  [Fintype I]
  [DecidableEq I]
  {state next : PartialForestNonbacktrackingState A}
-- given
  (step : A -> A ⊕ B)
  (hloopFree : ∀ current next, step current = Sum.inl next -> next ≠ current)
  (hstep : partialForestNonbacktrackingStep step hloopFree state = Sum.inl next) :
-- imply
  step next.1.1 = Sum.inl next.1.2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.partialForestNonbacktrackingStep_eq_inl_relation step hloopFree state next hstep

/--
[CanonicalStableRawComponentBalancedDirectBlock.postSecondContinuationAdvance_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma postSecondContinuationAdvance_invariant_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {entrance : Fin block.size}
  {n : Nat} :
-- imply
  let state := (block.postSecondContinuationAdvance entrance)^[n] (block.postSecondInitialState entrance) block.postSecondStep entrance state.1.1 = Sum.inl state.1.2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.postSecondContinuationAdvance_invariant block entrance n

/--
[CanonicalStableRawComponentBalancedDirectBlock.HasPostSecondBacktrack.exists_twoCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_twoCycle_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {entrance : Fin block.size}
-- given
  (hback : block.HasPostSecondBacktrack entrance) :
-- imply
  ∃ previous current : block.PostSecondState, previous ≠ current ∧ block.postSecondStep entrance previous = Sum.inl current ∧ block.postSecondStep entrance current = Sum.inl previous := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.HasPostSecondBacktrack.exists_twoCycle hback

/--
[CanonicalStableRawComponentBalancedDirectBlock.HasPostSecondBacktrack.exists_directIndexTwoCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma exists_directIndexTwoCycle_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {entrance : Fin block.size}
-- given
  (hback : block.HasPostSecondBacktrack entrance) :
-- imply
  ∃ previous current : Fin block.size, previous ≠ current ∧ block.directSuccessorStep previous = Sum.inl current ∧ block.directSuccessorStep current = Sum.inl previous := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.HasPostSecondBacktrack.exists_directIndexTwoCycle hback

/--
[CanonicalStableRawComponentBalancedDirectBlock.HasPostSecondBacktrack.threeTokens_or_directTwoCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma threeTokens_or_directTwoCycle_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
  {entrance : Fin block.size}
-- given
  (hback : block.HasPostSecondBacktrack entrance) :
-- imply
  let sources := finiteEmbeddingBlock block.size block.sourceBlock Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨ ∃ previous current : Fin block.size, previous ≠ current ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component (block.sourceBlock previous) = Sum.inl (block.directs current) ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component (block.sourceBlock current) = Sum.inl (block.directs previous) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.HasPostSecondBacktrack.threeTokens_or_directTwoCycle hback

/--
[CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_augmented_or_threeTokens_or_cycle_or_terminal_or_rankDrop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma growth_or_self_or_augmented_or_threeTokens_or_cycle_or_terminal_or_rankDrop_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (hcross : block.HasGeometricCrossing) :
-- imply
  (∃ extended : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) ∨ Nonempty (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ block.HasAugmentedIncidentBlock ∨ Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (finiteEmbeddingBlock block.size block.sourceBlock))) ∨ (∃ previous current : Fin block.size, previous ≠ current ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component (block.sourceBlock previous) = Sum.inl (block.directs current) ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component (block.sourceBlock current) = Sum.inl (block.directs previous)) ∨ (∃ entrance, block.HasPostSecondLongCycle entrance) ∨ Nonempty (CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ ∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p source.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_augmented_or_threeTokens_or_cycle_or_terminal_or_rankDrop hcross

/--
[CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit.smallerRecursion_or_finiteCycleDischarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean)
-/
@[path]
private lemma smallerRecursion_or_finiteCycleDischarge_eq
  [Fintype I]
  [DecidableEq I]
  {I : Type uI}
  {W : Type uW}
  [Fintype I]
  [DecidableEq I]
  [Fintype W]
  [DecidableEq W]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  [DecidableEq (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)]
  [DecidableEq (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)]
  {sources : Finset (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {orbit : CanonicalStableRawTightChargeOrbit ends m j k l zero hloop hjk hkl hk0 p hno component sources}
-- given
  (hresidual : orbit.HasBalancedResidualDeficit)
  (hdeficit : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ∃ block : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component, (block.IsClosed ∧ ∃ problem : FiniteRelationMinimalTightProblem.{uI, uI}, problem.rank < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component) ∧ ∀ source : block.StateComplement, ∀ token : CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component, CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component source.1 token -> token ∉ finiteEmbeddingBlock block.size block.tokenBlock) ∨ (∃ extended : CanonicalStableRawComponentBalancedDirectBlock ends m j k l zero hloop hjk hkl hk0 p hno component, extended.size = block.size + 1) ∨ Nonempty (CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ block.HasAugmentedIncidentBlock ∨ Nonempty (Fin 3 ↪ ↑(canonicalStableRawComponentIncidentNeighborhood ends m j k l zero hloop hjk hkl hk0 p hno component (finiteEmbeddingBlock block.size block.sourceBlock))) ∨ (∃ previous current : Fin block.size, previous ≠ current ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component (block.sourceBlock previous) = Sum.inl (block.directs current) ∧ canonicalStableRawComponentForestStep ends m j k l zero hloop hjk hkl hk0 p hno component (block.sourceBlock current) = Sum.inl (block.directs previous)) ∨ (∃ entrance, block.HasPostSecondLongCycle entrance) ∨ Nonempty (CanonicalStableRawComponentNonexceptionalToken ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ ∃ source : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧ canonicalStableRawSourceRank ends m j k l zero p u.source < canonicalStableRawSourceRank ends m j k l zero p source.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit.smallerRecursion_or_finiteCycleDischarge hresidual hdeficit


-- created on 2026-10-23
