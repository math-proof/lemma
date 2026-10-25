import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition.Part6
open Finset StatMech StatMech.FrontierD


/--
[sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {v : T.Vertex}
  {d : Fin 4} :
-- imply
  sixVertexLocalIncomingPattern omega v d ≠ sixVertexLocalIncomingPattern eta v d ↔ sixVertexTorusEdgeDisagrees omega eta (sixVertexTorusIncidentEdge T v d) := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees omega eta v d

/--
[sixVertexPositiveSeamDisagreements_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexPositiveSeamDisagreements_nonempty_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
-- given
  (homega : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (heta : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n) :
-- imply
  (sixVertexPositiveSeamDisagreements T omega eta).Nonempty := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveSeamDisagreements_nonempty T omega eta n homega heta hn

/--
[sixVertexLexPositiveSeamSeed_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexLexPositiveSeamSeed_mem_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
-- imply
  sixVertexLexPositiveSeamSeed T omega eta h ∈ sixVertexPositiveSeamDisagreements T omega eta := by
-- proof
  apply StatMech.FrontierD.sixVertexLexPositiveSeamSeed_mem T omega eta h

/--
[sixVertexLexPositiveSeamEdge_disagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexLexPositiveSeamEdge_disagrees_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
-- imply
  sixVertexTorusEdgeDisagrees omega eta (sixVertexLexPositiveSeamEdge T omega eta h) := by
-- proof
  apply StatMech.FrontierD.sixVertexLexPositiveSeamEdge_disagrees T omega eta h

/--
[sixVertexLexDisagreementComponentMask_seed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentMask_seed_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
-- imply
  (sixVertexLexDisagreementComponentMask T omega eta h).vertical (sixVertexLexPositiveSeamSeed T omega eta h, svFinLast T.height_pos) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentMask_seed T omega eta h

/--
[sixVertexLocalDisagreementCount_eq_two_or_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexLocalDisagreementCount_eq_two_or_four_eq
  {p q : SixVertexLocalIncomingPattern}
-- given
  (hp : p.Ice)
  (hq : q.Ice)
  (hne : p ≠ q) :
-- imply
  (∑ d, if p d ≠ q d then 1 else 0) = 2 \/ (∑ d, if p d ≠ q d then 1 else 0) = 4 := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalDisagreementCount_eq_two_or_four p q hp hq hne

/--
[sixVertexTorusLocalSwitchMask_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexTorusLocalSwitchMask_apply_eq
  {T : EvenTorus}
  {mask : SixVertexArrows T}
  {v : T.Vertex}
  {d : Fin 4} :
-- imply
  sixVertexTorusLocalSwitchMask mask v d = sixVertexTorusMaskSelects mask (sixVertexTorusIncidentEdge T v d) := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusLocalSwitchMask_apply mask v d

/--
[sixVertexLexDisagreementComponentMask_selects_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentMask_selects_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {e : SixVertexTorusEdge T}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
-- imply
  sixVertexTorusMaskSelects (sixVertexLexDisagreementComponentMask T omega eta h) e = true ↔ (sixVertexTorusDisagreementGraph omega eta).Reachable (sixVertexLexPositiveSeamEdge T omega eta h) e := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentMask_selects_iff T omega eta h e

/--
[sixVertexDisagreementGraph_reachable_disagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexDisagreementGraph_reachable_disagrees_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed e : SixVertexTorusEdge T}
-- given
  (hseed : sixVertexTorusEdgeDisagrees omega eta seed)
  (hreach : (sixVertexTorusDisagreementGraph omega eta).Reachable seed e) :
-- imply
  sixVertexTorusEdgeDisagrees omega eta e := by
-- proof
  apply StatMech.FrontierD.sixVertexDisagreementGraph_reachable_disagrees hseed hreach

/--
[sixVertexLexDisagreementComponentMask_selects_only_disagreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentMask_selects_only_disagreement_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {e : SixVertexTorusEdge T}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
  (he : sixVertexTorusMaskSelects (sixVertexLexDisagreementComponentMask T omega eta h) e = true) :
-- imply
  sixVertexTorusEdgeDisagrees omega eta e := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentMask_selects_only_disagreement T omega eta h e he

/--
[sixVertexLexDisagreementComponentMask_incident_closure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentMask_incident_closure_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {v : T.Vertex}
  {d r : Fin 4}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
  (hd : sixVertexTorusLocalSwitchMask (sixVertexLexDisagreementComponentMask T omega eta h) v d = true)
  (hr : sixVertexLocalIncomingPattern omega v r ≠ sixVertexLocalIncomingPattern eta v r) :
-- imply
  sixVertexTorusLocalSwitchMask (sixVertexLexDisagreementComponentMask T omega eta h) v r = true := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentMask_incident_closure T omega eta h v d r hd hr

/--
[sixVertexLexDisagreementComponentMask_local_eq_disagreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentMask_local_eq_disagreement_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {v : T.Vertex}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
  (hactive : ∃ d, sixVertexTorusLocalSwitchMask (sixVertexLexDisagreementComponentMask T omega eta h) v d = true) :
-- imply
  forall r, sixVertexTorusLocalSwitchMask (sixVertexLexDisagreementComponentMask T omega eta h) v r = decide (sixVertexLocalIncomingPattern omega v r ≠ sixVertexLocalIncomingPattern eta v r) := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentMask_local_eq_disagreement T omega eta h v hactive

/--
[sixVertexLexDisagreementComponentMask_local_route_size](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentMask_local_route_size_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
-- imply
  sixVertexLocalSwitchMaskCount (sixVertexTorusLocalSwitchMask (sixVertexLexDisagreementComponentMask T omega eta h) v) = 0 \/ sixVertexLocalSwitchMaskCount (sixVertexTorusLocalSwitchMask (sixVertexLexDisagreementComponentMask T omega eta h) v) = 2 \/ sixVertexLocalSwitchMaskCount (sixVertexTorusLocalSwitchMask (sixVertexLexDisagreementComponentMask T omega eta h) v) = 4 := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentMask_local_route_size T omega eta homega heta h v

/--
[sixVertexLocalSwapMask_eq_pair_of_disagreementMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexLocalSwapMask_eq_pair_of_disagreementMask_eq
  {p q mask : SixVertexLocalIncomingPattern}
-- given
  (hmask : forall d, mask d = decide (p d ≠ q d)) :
-- imply
  sixVertexLocalSwapMask p q mask = (q, p) := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalSwapMask_eq_pair_of_disagreementMask p q mask hmask

/--
[sixVertexLexDisagreementComponentSwitch_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentSwitch_ice_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
-- imply
  (sixVertexTorusSwitchFirst (sixVertexLexDisagreementComponentMask T omega eta h) omega eta).IceRule /\ (sixVertexTorusSwitchSecond (sixVertexLexDisagreementComponentMask T omega eta h) omega eta).IceRule := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentSwitch_ice T omega eta homega heta h

/--
[sixVertexTorusEdgeDisagrees_pairSwitch_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexTorusEdgeDisagrees_pairSwitch_iff_eq
  {T : EvenTorus}
  {mask omega eta : SixVertexArrows T}
  {e : SixVertexTorusEdge T} :
-- imply
  sixVertexTorusEdgeDisagrees (sixVertexTorusSwitchFirst mask omega eta) (sixVertexTorusSwitchSecond mask omega eta) e ↔ sixVertexTorusEdgeDisagrees omega eta e := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusEdgeDisagrees_pairSwitch_iff mask omega eta e

/--
[sixVertexTorusDisagreementGraph_pairSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean)
-/
@[path]
private lemma sixVertexTorusDisagreementGraph_pairSwitch_eq
  {T : EvenTorus}
  {mask omega eta : SixVertexArrows T} :
-- imply
  sixVertexTorusDisagreementGraph (sixVertexTorusSwitchFirst mask omega eta) (sixVertexTorusSwitchSecond mask omega eta) = sixVertexTorusDisagreementGraph omega eta := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusDisagreementGraph_pairSwitch mask omega eta


-- created on 2026-10-23
