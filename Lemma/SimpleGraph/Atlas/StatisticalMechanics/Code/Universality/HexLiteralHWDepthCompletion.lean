import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion
open StatMech StatMech.Universality


/--
[hlhda_prefixAugment_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_prefixAugment_ne_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  hlhda_prefixAugment ts hleg ≠ [] := by
-- proof
  apply StatMech.Universality.hlhda_prefixAugment_ne ts hleg

/--
[hlhda_suffixAugment_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_suffixAugment_ne_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  hlhda_suffixAugment ts hleg ≠ [] := by
-- proof
  apply StatMech.Universality.hlhda_suffixAugment_ne ts hleg

/--
[hlhda_terminalEdge_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_terminalEdge_spec_eq
  {ws : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ws).IsLegalSAW)
  (hne : ws ≠ []) :
-- imply
  hexAWNeighbor (hlhc_prefixCoord ws hleg.1 (ws.length - 1)) (hlhda_terminalEdge ws hleg hne) = hlhc_prefixCoord ws hleg.1 ws.length := by
-- proof
  apply StatMech.Universality.hlhda_terminalEdge_spec ws hleg hne

/--
[hlhda_completedPrefix_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_completedPrefix_length_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  (hlhda_completedPrefix ts hleg).length = (hlhda_prefixAugment ts hleg).length + 1 := by
-- proof
  apply StatMech.Universality.hlhda_completedPrefix_length ts hleg

/--
[hlhda_completedSuffix_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_completedSuffix_length_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  (hlhda_completedSuffix ts hleg).length = (hlhda_suffixAugment ts hleg).length := by
-- proof
  apply StatMech.Universality.hlhda_completedSuffix_length ts hleg

/--
[hlhda_completedPair_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_completedPair_length_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  (hlhda_completedPair ts hleg).1.length + (hlhda_completedPair ts hleg).2.length = ts.length + 5 := by
-- proof
  apply StatMech.Universality.hlhda_completedPair_length ts hleg

/--
[hlhda_eraseCompletion_completed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_eraseCompletion_completed_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  hlhda_eraseCompletion (hlhda_completedPair ts hleg) = hlhda_augmentedPair ts hleg := by
-- proof
  apply StatMech.Universality.hlhda_eraseCompletion_completed ts hleg

/--
[hlhda_completedPair_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_completedPair_injective_eq
  {xs ys : List ℤ}
-- given
  (hx : (ofTurns hexAWStart 1 xs).IsLegalSAW)
  (hy : (ofTurns hexAWStart 1 ys).IsLegalSAW)
  (heq : hlhda_completedPair xs hx = hlhda_completedPair ys hy) :
-- imply
  xs = ys := by
-- proof
  apply StatMech.Universality.hlhda_completedPair_injective hx hy heq

/--
[hlhda_decodeCompletedPair_completed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_decodeCompletedPair_completed_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  hlhda_decodeCompletedPair (hlhda_completedPair ts hleg) = ts := by
-- proof
  apply StatMech.Universality.hlhda_decodeCompletedPair_completed ts hleg

/--
[HLHDAEndpointColumnWalk.prefix_mem_vertexSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma prefix_mem_vertexSet_eq
  {T : ℕ}
  {ts : List ℤ}
  {W : HLHDAEndpointColumnWalk T ts}
  {k : ℕ}
-- given
  (hk : k < ts.length) :
-- imply
  hlhc_prefixCoord ts W.legal.1 k ∈ hexCSVertexSet T W.stripHeight := by
-- proof
  apply StatMech.Universality.HLHDAEndpointColumnWalk.prefix_mem_vertexSet W hk

/--
[HLHDAEndpointColumnWalk.top_mem_vertexSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma top_mem_vertexSet_eq
  {T : ℕ}
  {ts : List ℤ}
  {W : HLHDAEndpointColumnWalk T ts}
-- given
  (hT : 0 < T) :
-- imply
  W.topCoord ∈ hexCSVertexSet T W.stripHeight := by
-- proof
  apply StatMech.Universality.HLHDAEndpointColumnWalk.top_mem_vertexSet W hT

/--
[HLHDAEndpointColumnWalk.mem_topAtWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma mem_topAtWidth_eq
  {T : ℕ}
  {ts : List ℤ}
  {W : HLHDAEndpointColumnWalk T ts}
-- given
  (hT : 0 < T) :
-- imply
  HexCSTopWalkAtWidth T hT ts := by
-- proof
  apply StatMech.Universality.HLHDAEndpointColumnWalk.mem_topAtWidth W hT

/--
[hlhda_prefixCoord_eq_of_take_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_prefixCoord_eq_of_take_eq_eq
  {xs ys : List ℤ}
  {k : ℕ}
-- given
  (hx : (ofTurns hexAWStart 1 xs).LegalTurns)
  (hy : (ofTurns hexAWStart 1 ys).LegalTurns)
  (htake : xs.take k = ys.take k) :
-- imply
  hlhc_prefixCoord xs hx k = hlhc_prefixCoord ys hy k := by
-- proof
  apply StatMech.Universality.hlhda_prefixCoord_eq_of_take_eq hx hy k htake

/--
[hlhda_prefixCoord_append_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_prefixCoord_append_of_le_eq
  {xs tail : List ℤ}
  {k : ℕ}
-- given
  (hx : (ofTurns hexAWStart 1 xs).LegalTurns)
  (hout : (ofTurns hexAWStart 1 (xs ++ tail)).LegalTurns)
  (hk : k ≤ xs.length) :
-- imply
  hlhc_prefixCoord (xs ++ tail) hout k = hlhc_prefixCoord xs hx k := by
-- proof
  apply StatMech.Universality.hlhda_prefixCoord_append_of_le xs tail hx hout hk

/--
[hlhda_coordRun_translate_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_coordRun_translate_pos_eq
  {q p d : HexReturnCoord}
  {ws : List ℤ} :
-- imply
  (hlhr_coordRun (q.add p) d ws).pos = q.add (hlhr_coordRun p d ws).pos := by
-- proof
  apply StatMech.Universality.hlhda_coordRun_translate_pos q p d ws

/--
[hlhda_add_neg_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_add_neg_left_eq
  {p q : HexReturnCoord} :
-- imply
  p.add ((hlha_negCoord p).add q) = q := by
-- proof
  apply StatMech.Universality.hlhda_add_neg_left p q

/--
[hlhda_coordRun_neg_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_coordRun_neg_pos_eq
  {p d : HexReturnCoord}
  {ws : List ℤ}
-- given
  (hlegal : ∀ t ∈ ws, t = 1 ∨ t = -1) :
-- imply
  (hlhr_coordRun (hlha_negCoord p) (hlha_negCoord d) ws).pos = hlha_negCoord (hlhr_coordRun p d ws).pos := by
-- proof
  apply StatMech.Universality.hlhda_coordRun_neg_pos p d ws hlegal

/--
[hlhda_coordRun_augmentSide_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_coordRun_augmentSide_pos_eq
  {d : HexReturnCoord}
  {internal : List ℤ}
-- given
  (hd : HLHDAInwardDir d) :
-- imply
  (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base (hlhda_augmentSide d internal)).pos = hlhda_spacerRoot.add (hlhr_coordRun (HexReturnCoord.zero.add d) d internal).pos := by
-- proof
  apply StatMech.Universality.hlhda_coordRun_augmentSide_pos d internal hd

/--
[hlhda_spacer_normalized_depth_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_spacer_normalized_depth_color_eq
  {source c out : HexAWCoord}
-- given
  (hsource : source.color = .white)
  (hpos : hexAWReturnPos out = hlhda_spacerRoot.add ((hexAWReturnPos source).add (hlha_negCoord (hexAWReturnPos c)))) :
-- imply
  out.color = hlhd_swapColor c.color ∧ hexAWDepth out = hexAWDepth source - hexAWDepth c + 1 := by
-- proof
  apply StatMech.Universality.hlhda_spacer_normalized_depth_color source c out hsource hpos

/--
[hlhda_spacerWhite_depth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_spacerWhite_depth_eq
  {c : HexAWCoord}
-- given
  (hpos : hexAWReturnPos c = hlhda_spacerWhite) :
-- imply
  c.color = .white ∧ hexAWDepth c = 1 := by
-- proof
  apply StatMech.Universality.hlhda_spacerWhite_depth c hpos

/--
[hlhda_augmentSide_depth_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_augmentSide_depth_bounds_eq
  {d : HexReturnCoord}
  {internal : List ℤ}
  {source : HexAWCoord}
  {M : ℕ}
-- given
  (hd : HLHDAInwardDir d)
  (hraw : (ofTurns hexAWStart 1 (hlhda_augmentSide d internal)).IsLegalSAW)
  (hsourceWhite : source.color = .white)
  (hsourceDepth : hexAWDepth source = M)
  (hnormalized : ∀ q ∈ hlha_edgeVertices HexReturnCoord.zero d internal, ∃ c : HexAWCoord, 0 ≤ hexAWDepth c ∧ hexAWDepth c ≤ M ∧ q = (hexAWReturnPos source).add (hlha_negCoord (hexAWReturnPos c))) :
-- imply
  ∀ j, j ≤ (hlhda_augmentSide d internal).length → 0 ≤ hlhd_depth (hlhda_augmentSide d internal) hraw j ∧ hlhd_depth (hlhda_augmentSide d internal) hraw j ≤ M + 1 := by
-- proof
  apply StatMech.Universality.hlhda_augmentSide_depth_bounds d internal hd hraw source hsourceWhite M hsourceDepth hnormalized

/--
[hlhda_depth_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_depth_congr_eq
  {xs ys : List ℤ}
  {hx : (ofTurns hexAWStart 1 xs).IsLegalSAW}
  {hy : (ofTurns hexAWStart 1 ys).IsLegalSAW}
  {k : ℕ}
-- given
  (hxy : xs = ys) :
-- imply
  hlhd_depth xs hx k = hlhd_depth ys hy k := by
-- proof
  apply StatMech.Universality.hlhda_depth_congr hxy k

/--
[hlhda_prefixAugment_depth_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_prefixAugment_depth_bounds_eq
  {ts : List ℤ}
  {M : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hM : 0 < M)
  (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
  (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
-- imply
  ∀ j, j ≤ (hlhda_prefixAugment ts hleg).length → 0 ≤ hlhd_depth (hlhda_prefixAugment ts hleg) (hlhda_prefixAugment_isLegalSAW ts hleg) j ∧ hlhd_depth (hlhda_prefixAugment ts hleg) (hlhda_prefixAugment_isLegalSAW ts hleg) j ≤ M + 1 := by
-- proof
  apply StatMech.Universality.hlhda_prefixAugment_depth_bounds hleg M hM hnonneg hcut

/--
[hlhda_suffix_initial_notFlat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_suffix_initial_notFlat_eq
  {ts : List ℤ}
  {M : ℕ}
  {t : ℤ}
  {us : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hM : 0 < M)
  (hend : hlhd_depth ts hleg ts.length = 0)
  (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ))
  (hsuf : ts.drop (hlhda_cutPos ts hleg) = t :: us) :
-- imply
  hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t) ≠ hlhda_flatNeighbor := by
-- proof
  apply StatMech.Universality.hlhda_suffix_initial_notFlat hleg M hM hend hcut hsuf

/--
[hlhda_suffixAugment_depth_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_suffixAugment_depth_bounds_eq
  {ts : List ℤ}
  {M : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hM : 0 < M)
  (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
  (hend : hlhd_depth ts hleg ts.length = 0)
  (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
-- imply
  ∀ j, j ≤ (hlhda_suffixAugment ts hleg).length → 0 ≤ hlhd_depth (hlhda_suffixAugment ts hleg) (hlhda_suffixAugment_isLegalSAW ts hleg) j ∧ hlhd_depth (hlhda_suffixAugment ts hleg) (hlhda_suffixAugment_isLegalSAW ts hleg) j ≤ M + 1 := by
-- proof
  apply StatMech.Universality.hlhda_suffixAugment_depth_bounds hleg M hM hnonneg hend hcut

/--
[hlhda_prefixAugment_final_returnPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_prefixAugment_final_returnPos_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hne : ts ≠ []) :
-- imply
  hexAWReturnPos (hlhc_prefixCoord (hlhda_prefixAugment ts hleg) (hlhda_prefixAugment_isLegalSAW ts hleg).1 (hlhda_prefixAugment ts hleg).length) = hlhda_spacerRoot.add (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg))) := by
-- proof
  apply StatMech.Universality.hlhda_prefixAugment_final_returnPos hleg hne

/--
[hlhda_prefixAugment_final_color_depth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_prefixAugment_final_color_depth_eq
  {ts : List ℤ}
  {M : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hM : 0 < M)
  (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
-- imply
  let raw := hlhda_prefixAugment ts hleg let hraw := hlhda_prefixAugment_isLegalSAW ts hleg (hlhc_prefixCoord raw hraw.1 raw.length).color = .white ∧ hlhd_depth raw hraw raw.length = M + 1 := by
-- proof
  apply StatMech.Universality.hlhda_prefixAugment_final_color_depth hleg M hM hcut

/--
[hlhda_suffixAugment_final_returnPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_suffixAugment_final_returnPos_eq
  {ts : List ℤ}
  {M : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hM : 0 < M)
  (hend : hlhd_depth ts hleg ts.length = 0)
  (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
-- imply
  hexAWReturnPos (hlhc_prefixCoord (hlhda_suffixAugment ts hleg) (hlhda_suffixAugment_isLegalSAW ts hleg).1 (hlhda_suffixAugment ts hleg).length) = hlhda_spacerRoot.add ((hexAWReturnPos (hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg))).add (hlha_negCoord (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 ts.length)))) := by
-- proof
  apply StatMech.Universality.hlhda_suffixAugment_final_returnPos hleg M hM hend hcut

/--
[hlhda_suffixAugment_final_color_depth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_suffixAugment_final_color_depth_eq
  {ts : List ℤ}
  {M : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hM : 0 < M)
  (hend : hlhd_depth ts hleg ts.length = 0)
  (hendWhite : (hlhc_prefixCoord ts hleg.1 ts.length).color = .white)
  (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
-- imply
  let raw := hlhda_suffixAugment ts hleg let hraw := hlhda_suffixAugment_isLegalSAW ts hleg (hlhc_prefixCoord raw hraw.1 raw.length).color = .black ∧ hlhd_depth raw hraw raw.length = M + 1 := by
-- proof
  apply StatMech.Universality.hlhda_suffixAugment_final_color_depth hleg M hM hend hendWhite hcut

/--
[hlhda_prefixTerminalEdge_inward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_prefixTerminalEdge_inward_eq
  {ts : List ℤ}
  {M : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hM : 0 < M)
  (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
  (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
-- imply
  let raw := hlhda_prefixAugment ts hleg let hraw := hlhda_prefixAugment_isLegalSAW ts hleg let e := hlhda_terminalEdge raw hraw (hlhda_prefixAugment_ne ts hleg) e = 1 ∨ e = 2 := by
-- proof
  apply StatMech.Universality.hlhda_prefixTerminalEdge_inward hleg M hM hnonneg hcut

/--
[hlhda_completedPrefix_endpointIsLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_completedPrefix_endpointIsLegalSAW_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  (ofTurns hexAWStart 1 (hlhda_completedPrefix ts hleg)).EndpointIsLegalSAW := by
-- proof
  apply StatMech.Universality.hlhda_completedPrefix_endpointIsLegalSAW ts hleg

/--
[hlhda_completedPrefix_endsAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_completedPrefix_endsAt_eq
  {ts : List ℤ}
  {M : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hM : 0 < M)
  (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
  (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
-- imply
  let raw := hlhda_prefixAugment ts hleg let hraw := hlhda_prefixAugment_isLegalSAW ts hleg let far := hlhc_prefixCoord raw hraw.1 raw.length (ofTurns hexAWStart 1 (hlhda_completedPrefix ts hleg)).EndsAt (hexAWMid far 0) := by
-- proof
  apply StatMech.Universality.hlhda_completedPrefix_endsAt hleg M hM hnonneg hcut

/--
[hlhda_completedPrefix_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_completedPrefix_horizontal_eq
  {ts : List ℤ}
  {M : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hM : 0 < M)
  (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
  (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
-- imply
  ∀ k, k < (hlhda_completedPrefix ts hleg).length → 0 ≤ hexAWBookRe2 (hlhc_prefixCoord (hlhda_completedPrefix ts hleg) (hlhda_completedPrefix_endpointIsLegalSAW ts hleg).1 k) ∧ hexAWBookRe2 (hlhc_prefixCoord (hlhda_completedPrefix ts hleg) (hlhda_completedPrefix_endpointIsLegalSAW ts hleg).1 k) ≤ 3 * (M + 1) := by
-- proof
  apply StatMech.Universality.hlhda_completedPrefix_horizontal hleg M hM hnonneg hcut

/--
[hlhda_completedPrefix_mem_topAtWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_completedPrefix_mem_topAtWidth_eq
  {ts : List ℤ}
  {M : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hM : 0 < M)
  (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
  (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
-- imply
  HexCSTopWalkAtWidth (M + 1) (by omega) (hlhda_completedPrefix ts hleg) := by
-- proof
  apply StatMech.Universality.hlhda_completedPrefix_mem_topAtWidth hleg M hM hnonneg hcut

/--
[hlhda_prefixCoord_returnPos_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_prefixCoord_returnPos_legal_eq
  {ws : List ℤ}
  {k : ℕ}
-- given
  (hlegal : (ofTurns hexAWStart 1 ws).LegalTurns) :
-- imply
  (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base (ws.take k)).pos = hexAWReturnPos (hlhc_prefixCoord ws hlegal k) := by
-- proof
  apply StatMech.Universality.hlhda_prefixCoord_returnPos_legal ws hlegal k

/--
[hlhda_prefix_edge_unit_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_prefix_edge_unit_legal_eq
  {ws : List ℤ}
  {k : ℕ}
  {e : Fin 3}
-- given
  (hlegal : (ofTurns hexAWStart 1 ws).LegalTurns)
  (hk : k < ws.length)
  (he : hexAWNeighbor (hlhc_prefixCoord ws hlegal k) e = hlhc_prefixCoord ws hlegal (k + 1)) :
-- imply
  hexUnit (hexInfra_headAccum 1 (ws.take (k + 1))) = hexUnit (hexAWHeading (hlhc_prefixCoord ws hlegal k) e) := by
-- proof
  apply StatMech.Universality.hlhda_prefix_edge_unit_legal ws hlegal k hk e he

/--
[hlhda_coordVertices_append_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_coordVertices_append_single_eq
  {p d : HexReturnCoord}
  {ws : List ℤ}
  {t : ℤ} :
-- imply
  hlha_coordVertices p d (ws ++ [t]) = hlha_coordVertices p d ws ++ [(hlhr_coordRun p d ws).pos.add ((hlhr_coordRun p d ws).dir.turn t)] := by
-- proof
  apply StatMech.Universality.hlhda_coordVertices_append_single p d ws t

/--
[hlhda_suffixTerminalEdge_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_suffixTerminalEdge_zero_eq
  {ts : List ℤ}
  {M : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hM : 0 < M)
  (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
  (hend : hlhd_depth ts hleg ts.length = 0)
  (hendWhite : (hlhc_prefixCoord ts hleg.1 ts.length).color = .white)
  (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
-- imply
  let raw := hlhda_suffixAugment ts hleg let hraw := hlhda_suffixAugment_isLegalSAW ts hleg hlhda_terminalEdge raw hraw (hlhda_suffixAugment_ne ts hleg) = 0 := by
-- proof
  apply StatMech.Universality.hlhda_suffixTerminalEdge_zero hleg M hM hnonneg hend hendWhite hcut

/--
[hlhda_suffixAugment_terminal_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_suffixAugment_terminal_top_eq
  {ts : List ℤ}
  {M : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hM : 0 < M)
  (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
  (hend : hlhd_depth ts hleg ts.length = 0)
  (hendWhite : (hlhc_prefixCoord ts hleg.1 ts.length).color = .white)
  (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
-- imply
  let raw := hlhda_suffixAugment ts hleg let hraw := hlhda_suffixAugment_isLegalSAW ts hleg let top := hlhc_prefixCoord raw hraw.1 (raw.length - 1) top.color = .white ∧ hexAWDepth top = M + 1 ∧ (ofTurns hexAWStart 1 raw).EndsAt (hexAWMid top 0) := by
-- proof
  apply StatMech.Universality.hlhda_suffixAugment_terminal_top hleg M hM hnonneg hend hendWhite hcut

/--
[hlhda_completedSuffix_mem_topAtWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_completedSuffix_mem_topAtWidth_eq
  {ts : List ℤ}
  {M : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hM : 0 < M)
  (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
  (hend : hlhd_depth ts hleg ts.length = 0)
  (hendWhite : (hlhc_prefixCoord ts hleg.1 ts.length).color = .white)
  (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
-- imply
  HexCSTopWalkAtWidth (M + 1) (by omega) (hlhda_completedSuffix ts hleg) := by
-- proof
  apply StatMech.Universality.hlhda_completedSuffix_mem_topAtWidth hleg M hM hnonneg hend hendWhite hcut

/--
[hlhda_completedPair_mem_topAtWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean)
-/
@[path]
private lemma hlhda_completedPair_mem_topAtWidth_eq
  {ts : List ℤ}
  {M : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hM : 0 < M)
  (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
  (hend : hlhd_depth ts hleg ts.length = 0)
  (hendWhite : (hlhc_prefixCoord ts hleg.1 ts.length).color = .white)
  (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
-- imply
  HexCSTopWalkAtWidth (M + 1) (by omega) (hlhda_completedPair ts hleg).1 ∧ HexCSTopWalkAtWidth (M + 1) (by omega) (hlhda_completedPair ts hleg).2 := by
-- proof
  apply StatMech.Universality.hlhda_completedPair_mem_topAtWidth hleg M hM hnonneg hend hendWhite hcut


-- created on 2026-10-23
