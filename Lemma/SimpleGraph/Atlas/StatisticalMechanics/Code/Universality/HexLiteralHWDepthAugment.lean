import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
open StatMech StatMech.Universality


/--
[hlhda_returnPos_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_returnPos_injective_eq :
-- imply
  Function.Injective hexAWReturnPos := by
-- proof
  apply StatMech.Universality.hlhda_returnPos_injective

/--
[hlhda_coordRuns_pos_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_coordRuns_pos_eq_eq
  {p d : HexReturnCoord}
  {ts : List ℤ} :
-- imply
  (hlhr_coordRun p d ts).pos = (hexEndpointCoordRun p d ts).pos := by
-- proof
  apply StatMech.Universality.hlhda_coordRuns_pos_eq p d ts

/--
[hlhda_prefixCoord_returnPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_prefixCoord_returnPos_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base (ts.take k)).pos = hexAWReturnPos (hlhc_prefixCoord ts hleg.1 k) := by
-- proof
  apply StatMech.Universality.hlhda_prefixCoord_returnPos ts hleg k

/--
[hlhda_prefixCoord_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_prefixCoord_zero_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  hlhc_prefixCoord ts hleg.1 0 = hexAWOriginCoord := by
-- proof
  apply StatMech.Universality.hlhda_prefixCoord_zero ts hleg

/--
[hlhda_depth_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_depth_zero_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  hlhd_depth ts hleg 0 = 0 := by
-- proof
  apply StatMech.Universality.hlhda_depth_zero ts hleg

/--
[hlhda_depth_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_depth_one_eq
  {t : ℤ}
  {us : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 (t :: us)).IsLegalSAW) :
-- imply
  hlhd_depth (t :: us) hleg 1 = 1 := by
-- proof
  apply StatMech.Universality.hlhda_depth_one t us hleg

/--
[hlhda_returnScore_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_returnScore_exact_eq
  {c : HexAWCoord} :
-- imply
  2 * (hexAWReturnPos c).x - (hexAWReturnPos c).y = match c.color with := by
-- proof
  apply StatMech.Universality.hlhda_returnScore_exact c

/--
[hlhda_depth_pos_of_returnScore_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_depth_pos_of_returnScore_pos_eq
  {c : HexAWCoord}
-- given
  (hscore : 0 < 2 * (hexAWReturnPos c).x - (hexAWReturnPos c).y) :
-- imply
  0 < hexAWDepth c := by
-- proof
  apply StatMech.Universality.hlhda_depth_pos_of_returnScore_pos c hscore

/--
[hlhda_exists_firstMax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_exists_firstMax_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  ∃ cp, cp ≤ ts.length ∧ (∀ k ≤ ts.length, hlhd_depth ts hleg k ≤ hlhd_depth ts hleg cp) ∧ ∀ k, k < cp → hlhd_depth ts hleg k < hlhd_depth ts hleg cp := by
-- proof
  apply StatMech.Universality.hlhda_exists_firstMax ts hleg

/--
[hlhda_cutPos_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_cutPos_le_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  hlhda_cutPos ts hleg ≤ ts.length := by
-- proof
  apply StatMech.Universality.hlhda_cutPos_le ts hleg

/--
[hlhda_cutPos_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_cutPos_max_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hk : k ≤ ts.length) :
-- imply
  hlhd_depth ts hleg k ≤ hlhd_depth ts hleg (hlhda_cutPos ts hleg) := by
-- proof
  apply StatMech.Universality.hlhda_cutPos_max ts hleg k hk

/--
[hlhda_cutPos_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_cutPos_first_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hk : k < hlhda_cutPos ts hleg) :
-- imply
  hlhd_depth ts hleg k < hlhd_depth ts hleg (hlhda_cutPos ts hleg) := by
-- proof
  apply StatMech.Universality.hlhda_cutPos_first ts hleg k hk

/--
[hlhda_cutPos_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_cutPos_pos_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hne : ts ≠ []) :
-- imply
  0 < hlhda_cutPos ts hleg := by
-- proof
  apply StatMech.Universality.hlhda_cutPos_pos hleg hne

/--
[hlhda_firstDir_mem_edgeVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_firstDir_mem_edgeVertices_eq
  {d : HexReturnCoord}
  {ts : List ℤ} :
-- imply
  d ∈ hlha_edgeVertices HexReturnCoord.zero d ts := by
-- proof
  apply StatMech.Universality.hlhda_firstDir_mem_edgeVertices d ts

/--
[hlhda_halfSpace_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_halfSpace_congr_eq
  {xs ys : List ℤ}
  {hx : (ofTurns hexAWStart 1 xs).IsLegalSAW}
  {hy : (ofTurns hexAWStart 1 ys).IsLegalSAW}
-- given
  (hxy : xs = ys)
  (hhalf : HLHDLiteralHalfSpace xs hx) :
-- imply
  HLHDLiteralHalfSpace ys hy := by
-- proof
  apply StatMech.Universality.hlhda_halfSpace_congr hxy hhalf

/--
[hlhda_entryTurn_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_entryTurn_legal_eq
  {d : HexReturnCoord} :
-- imply
  hlhda_entryTurn d = 1 ∨ hlhda_entryTurn d = -1 := by
-- proof
  apply StatMech.Universality.hlhda_entryTurn_legal d

/--
[hlhda_entryTurn_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_entryTurn_dir_eq
  {d : HexReturnCoord}
-- given
  (hd : HLHDAInwardDir d) :
-- imply
  HexReturnCoord.base.turn (hlhda_entryTurn d) = d := by
-- proof
  apply StatMech.Universality.hlhda_entryTurn_dir hd

/--
[hlhda_augmentSide_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_augmentSide_length_eq
  {d : HexReturnCoord}
  {internal : List ℤ} :
-- imply
  (hlhda_augmentSide d internal).length = internal.length + 3 := by
-- proof
  apply StatMech.Universality.hlhda_augmentSide_length d internal

/--
[hlhda_emptySide_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_emptySide_length_eq :
-- imply
  hlhda_emptySide.length = 2 := by
-- proof
  apply StatMech.Universality.hlhda_emptySide_length

/--
[hlhda_augmentSide_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_augmentSide_legal_eq
  {d : HexReturnCoord}
  {internal : List ℤ}
-- given
  (hlegal : ∀ t ∈ internal, t = 1 ∨ t = -1) :
-- imply
  (ofTurns hexAWStart 1 (hlhda_augmentSide d internal)).LegalTurns := by
-- proof
  apply StatMech.Universality.hlhda_augmentSide_legal d internal hlegal

/--
[hlhda_emptySide_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_emptySide_legal_eq :
-- imply
  (ofTurns hexAWStart 1 hlhda_emptySide).LegalTurns := by
-- proof
  apply StatMech.Universality.hlhda_emptySide_legal

/--
[hlhda_coordVertices_augmentSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_coordVertices_augmentSide_eq
  {d : HexReturnCoord}
  {internal : List ℤ}
-- given
  (hd : HLHDAInwardDir d) :
-- imply
  hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base (hlhda_augmentSide d internal) = HexReturnCoord.zero :: hlhda_spacerWhite :: (hlha_edgeVertices HexReturnCoord.zero d internal).map hlhda_spacerRoot.add := by
-- proof
  apply StatMech.Universality.hlhda_coordVertices_augmentSide d internal hd

/--
[hlhda_coordVertices_emptySide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_coordVertices_emptySide_eq :
-- imply
  hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base hlhda_emptySide = [HexReturnCoord.zero, hlhda_spacerWhite, hlhda_spacerRoot] := by
-- proof
  apply StatMech.Universality.hlhda_coordVertices_emptySide

/--
[hlhda_score_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_score_zero_eq :
-- imply
  hlhda_score HexReturnCoord.zero = 0 := by
-- proof
  apply StatMech.Universality.hlhda_score_zero

/--
[hlhda_score_spacerWhite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_score_spacerWhite_eq :
-- imply
  hlhda_score hlhda_spacerWhite = 1 := by
-- proof
  apply StatMech.Universality.hlhda_score_spacerWhite

/--
[hlhda_score_spacerRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_score_spacerRoot_eq :
-- imply
  hlhda_score hlhda_spacerRoot = 3 := by
-- proof
  apply StatMech.Universality.hlhda_score_spacerRoot

/--
[hlhda_score_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_score_add_eq
  {p q : HexReturnCoord} :
-- imply
  hlhda_score (p.add q) = hlhda_score p + hlhda_score q := by
-- proof
  apply StatMech.Universality.hlhda_score_add p q

/--
[hlhda_spacerRoot_add_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_spacerRoot_add_ne_zero_eq
  {p : HexReturnCoord}
-- given
  (hp : -2 ≤ hlhda_score p) :
-- imply
  hlhda_spacerRoot.add p ≠ HexReturnCoord.zero := by
-- proof
  apply StatMech.Universality.hlhda_spacerRoot_add_ne_zero p hp

/--
[hlhda_spacerRoot_add_eq_white_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_spacerRoot_add_eq_white_iff_eq
  {p : HexReturnCoord} :
-- imply
  hlhda_spacerRoot.add p = hlhda_spacerWhite ↔ p = hlhda_flatNeighbor := by
-- proof
  apply StatMech.Universality.hlhda_spacerRoot_add_eq_white_iff p

/--
[hlhda_coordVertices_augmentSide_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_coordVertices_augmentSide_nodup_eq
  {d : HexReturnCoord}
  {internal : List ℤ}
-- given
  (hd : HLHDAInwardDir d)
  (hnodup : (hlha_edgeVertices HexReturnCoord.zero d internal).Nodup)
  (hscore : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d internal, -2 ≤ hlhda_score p)
  (hflat : hlhda_flatNeighbor ∉ hlha_edgeVertices HexReturnCoord.zero d internal) :
-- imply
  (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base (hlhda_augmentSide d internal)).Nodup := by
-- proof
  apply StatMech.Universality.hlhda_coordVertices_augmentSide_nodup d internal hd hnodup hscore hflat

/--
[hlhda_coordVertices_emptySide_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_coordVertices_emptySide_nodup_eq :
-- imply
  (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base hlhda_emptySide).Nodup := by
-- proof
  apply StatMech.Universality.hlhda_coordVertices_emptySide_nodup

/--
[hlhda_augmentSide_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_augmentSide_isLegalSAW_eq
  {d : HexReturnCoord}
  {internal : List ℤ}
-- given
  (hd : HLHDAInwardDir d)
  (hlegal : ∀ t ∈ internal, t = 1 ∨ t = -1)
  (hnodup : (hlha_edgeVertices HexReturnCoord.zero d internal).Nodup)
  (hscore : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d internal, -2 ≤ hlhda_score p)
  (hflat : hlhda_flatNeighbor ∉ hlha_edgeVertices HexReturnCoord.zero d internal) :
-- imply
  (ofTurns hexAWStart 1 (hlhda_augmentSide d internal)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlhda_augmentSide_isLegalSAW d internal hd hlegal hnodup hscore hflat

/--
[hlhda_emptySide_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_emptySide_isLegalSAW_eq :
-- imply
  (ofTurns hexAWStart 1 hlhda_emptySide).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlhda_emptySide_isLegalSAW

/--
[hlhda_augmentSide_runnerScore_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_augmentSide_runnerScore_pos_eq
  {d : HexReturnCoord}
  {internal : List ℤ}
  {k : ℕ}
-- given
  (hd : HLHDAInwardDir d)
  (hscore : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d internal, -2 ≤ hlhda_score p)
  (hk : 0 < k)
  (hkle : k ≤ (hlhda_augmentSide d internal).length) :
-- imply
  0 < hlhda_score (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ((hlhda_augmentSide d internal).take k)).pos := by
-- proof
  apply StatMech.Universality.hlhda_augmentSide_runnerScore_pos d internal hd hscore hk hkle

/--
[hlhda_emptySide_runnerScore_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_emptySide_runnerScore_pos_eq
  {k : ℕ}
-- given
  (hk : 0 < k)
  (hkle : k ≤ hlhda_emptySide.length) :
-- imply
  0 < hlhda_score (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base (hlhda_emptySide.take k)).pos := by
-- proof
  apply StatMech.Universality.hlhda_emptySide_runnerScore_pos hk hkle

/--
[hlhda_augmentSide_halfSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_augmentSide_halfSpace_eq
  {d : HexReturnCoord}
  {internal : List ℤ}
-- given
  (hd : HLHDAInwardDir d)
  (hlegal : ∀ t ∈ internal, t = 1 ∨ t = -1)
  (hnodup : (hlha_edgeVertices HexReturnCoord.zero d internal).Nodup)
  (hscore : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d internal, -2 ≤ hlhda_score p)
  (hflat : hlhda_flatNeighbor ∉ hlha_edgeVertices HexReturnCoord.zero d internal) :
-- imply
  HLHDLiteralHalfSpace (hlhda_augmentSide d internal) (hlhda_augmentSide_isLegalSAW d internal hd hlegal hnodup hscore hflat) := by
-- proof
  apply StatMech.Universality.hlhda_augmentSide_halfSpace d internal hd hlegal hnodup hscore hflat

/--
[hlhda_emptySide_halfSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_emptySide_halfSpace_eq :
-- imply
  HLHDLiteralHalfSpace hlhda_emptySide hlhda_emptySide_isLegalSAW := by
-- proof
  apply StatMech.Universality.hlhda_emptySide_halfSpace

/--
[hlhda_neighbor_color_black](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_neighbor_color_black_eq
  {c d : HexAWCoord}
  {e : Fin 3}
-- given
  (hc : c.color = .black)
  (h : hexAWNeighbor c e = d) :
-- imply
  d.color = .white := by
-- proof
  apply StatMech.Universality.hlhda_neighbor_color_black hc h

/--
[hlhda_neighbor_color_white](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_neighbor_color_white_eq
  {c d : HexAWCoord}
  {e : Fin 3}
-- given
  (hc : c.color = .white)
  (h : hexAWNeighbor c e = d) :
-- imply
  d.color = .black := by
-- proof
  apply StatMech.Universality.hlhda_neighbor_color_white hc h

/--
[hlhda_cut_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_cut_local_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hne : ts ≠ []) :
-- imply
  let cp := hlhda_cutPos ts hleg (hlhc_prefixCoord ts hleg.1 (cp - 1)).color = .black ∧ (hlhc_prefixCoord ts hleg.1 cp).color = .white ∧ hlhd_depth ts hleg cp = hlhd_depth ts hleg (cp - 1) + 1 := by
-- proof
  apply StatMech.Universality.hlhda_cut_local hleg hne

/--
[hlhda_coordRun_lastStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_coordRun_lastStep_eq
  {p d : HexReturnCoord}
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hk : 0 < k)
  (hkle : k ≤ ts.length) :
-- imply
  (hlhr_coordRun p d (ts.take k)).pos = ((hlhr_coordRun p d (ts.take (k - 1))).pos.add (hlhr_coordRun p d (ts.take k)).dir) := by
-- proof
  apply StatMech.Universality.hlhda_coordRun_lastStep p d ts hk hkle

/--
[hlhda_score_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_score_neg_eq
  {p : HexReturnCoord} :
-- imply
  hlhda_score (hlha_negCoord p) = -hlhda_score p := by
-- proof
  apply StatMech.Universality.hlhda_score_neg p

/--
[hlhda_inward_of_unit_score_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_inward_of_unit_score_one_eq
  {d : HexReturnCoord}
-- given
  (hu : d.IsUnit)
  (hs : hlhda_score d = 1) :
-- imply
  HLHDAInwardDir d := by
-- proof
  apply StatMech.Universality.hlhda_inward_of_unit_score_one d hu hs

/--
[hlhda_cutState_inward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_cutState_inward_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hne : ts ≠ []) :
-- imply
  HLHDAInwardDir (hlhda_cutState ts hleg).dir := by
-- proof
  apply StatMech.Universality.hlhda_cutState_inward hleg hne

/--
[hlhda_returnPos_normalize_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_returnPos_normalize_down_eq
  {source c : HexAWCoord}
-- given
  (hs : source.color = .white) :
-- imply
  hexAWReturnPos (hlhd_normalizeCoord false source c) = (hexAWReturnPos source).add (hlha_negCoord (hexAWReturnPos c)) := by
-- proof
  apply StatMech.Universality.hlhda_returnPos_normalize_down source c hs

/--
[hlhda_normalized_score_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_normalized_score_lower_eq
  {source c : HexAWCoord}
-- given
  (hs : source.color = .white)
  (hdepth : hexAWDepth c ≤ hexAWDepth source) :
-- imply
  -2 ≤ hlhda_score ((hexAWReturnPos source).add (hlha_negCoord (hexAWReturnPos c))) := by
-- proof
  apply StatMech.Universality.hlhda_normalized_score_lower source c hs hdepth

/--
[hlhda_normalized_eq_flat_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_normalized_eq_flat_iff_eq
  {source c : HexAWCoord}
-- given
  (hs : source.color = .white) :
-- imply
  (hexAWReturnPos source).add (hlha_negCoord (hexAWReturnPos c)) = hlhda_flatNeighbor ↔ c = hexAWNeighbor source 0 := by
-- proof
  apply StatMech.Universality.hlhda_normalized_eq_flat_iff source c hs

/--
[hlhda_depth_neighbor_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_depth_neighbor_zero_eq
  {c : HexAWCoord} :
-- imply
  hexAWDepth (hexAWNeighbor c 0) = hexAWDepth c := by
-- proof
  apply StatMech.Universality.hlhda_depth_neighbor_zero c

/--
[hlhda_add_neg_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_add_neg_add_eq
  {p q : HexReturnCoord} :
-- imply
  p.add (hlha_negCoord (p.add q)) = hlha_negCoord q := by
-- proof
  apply StatMech.Universality.hlhda_add_neg_add p q

/--
[hlhda_prefix_normalized_point](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_prefix_normalized_point_eq
  {ts : List ℤ}
  {t : ℤ}
  {us : List ℤ}
  {q : HexReturnCoord}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hpre : ts.take (hlhda_cutPos ts hleg) = t :: us)
  (hq : q ∈ hlha_edgeVertices HexReturnCoord.zero (hlhda_cutState ts hleg).dir (loopReverse us)) :
-- imply
  ∃ k, k ≤ hlhda_cutPos ts hleg ∧ q = (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg))).add (hlha_negCoord (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 k))) := by
-- proof
  apply StatMech.Universality.hlhda_prefix_normalized_point hleg hpre hq

/--
[hlhda_prefix_side_hypotheses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_prefix_side_hypotheses_eq
  {ts : List ℤ}
  {t : ℤ}
  {us : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hne : ts ≠ [])
  (hpre : ts.take (hlhda_cutPos ts hleg) = t :: us) :
-- imply
  let d := (hlhda_cutState ts hleg).dir HLHDAInwardDir d ∧ (∀ u ∈ loopReverse us, u = 1 ∨ u = -1) ∧ (hlha_edgeVertices HexReturnCoord.zero d (loopReverse us)).Nodup ∧ (∀ q ∈ hlha_edgeVertices HexReturnCoord.zero d (loopReverse us), -2 ≤ hlhda_score q) ∧ hlhda_flatNeighbor ∉ hlha_edgeVertices HexReturnCoord.zero d (loopReverse us) := by
-- proof
  apply StatMech.Universality.hlhda_prefix_side_hypotheses hleg hne hpre

/--
[hlhda_prefixAugment_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_prefixAugment_isLegalSAW_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  (ofTurns hexAWStart 1 (hlhda_prefixAugment ts hleg)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlhda_prefixAugment_isLegalSAW ts hleg

/--
[hlhda_prefixAugment_halfSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_prefixAugment_halfSpace_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  HLHDLiteralHalfSpace (hlhda_prefixAugment ts hleg) (hlhda_prefixAugment_isLegalSAW ts hleg) := by
-- proof
  apply StatMech.Universality.hlhda_prefixAugment_halfSpace ts hleg

/--
[hlhda_prefixAugment_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_prefixAugment_length_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  (hlhda_prefixAugment ts hleg).length = hlhda_cutPos ts hleg + 2 := by
-- proof
  apply StatMech.Universality.hlhda_prefixAugment_length ts hleg

/--
[hlhda_prefixAugment_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_prefixAugment_spec_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  (ofTurns hexAWStart 1 (hlhda_prefixAugment ts hleg)).IsLegalSAW ∧ HLHDLiteralHalfSpace (hlhda_prefixAugment ts hleg) (hlhda_prefixAugment_isLegalSAW ts hleg) ∧ (hlhda_prefixAugment ts hleg).length = hlhda_cutPos ts hleg + 2 := by
-- proof
  apply StatMech.Universality.hlhda_prefixAugment_spec ts hleg

/--
[hlhda_coordVertices_getElem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_coordVertices_getElem_eq
  {p d : HexReturnCoord}
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hk : k ≤ ts.length) :
-- imply
  (hlha_coordVertices p d ts)[k]'(by rw [hlha_coordVertices_length] omega) = (hlhr_coordRun p d (ts.take k)).pos := by
-- proof
  apply StatMech.Universality.hlhda_coordVertices_getElem p d ts k hk

/--
[hlhda_prefixCoord_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_prefixCoord_injective_eq
  {ts : List ℤ}
  {k l : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hk : k ≤ ts.length)
  (hl : l ≤ ts.length)
  (heq : hlhc_prefixCoord ts hleg.1 k = hlhc_prefixCoord ts hleg.1 l) :
-- imply
  k = l := by
-- proof
  apply StatMech.Universality.hlhda_prefixCoord_injective ts hleg hk hl heq

/--
[hlhda_cut_next_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_cut_next_state_eq
  {ts : List ℤ}
  {t : ℤ}
  {us : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hsuf : ts.drop (hlhda_cutPos ts hleg) = t :: us) :
-- imply
  hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base (ts.take (hlhda_cutPos ts hleg + 1)) = let r := hlhda_cutState ts hleg ⟨r.pos.add (r.dir.turn t), r.dir.turn t⟩ := by
-- proof
  apply StatMech.Universality.hlhda_cut_next_state hleg hsuf

/--
[hlhda_normalized_neighbor_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_normalized_neighbor_cases_eq
  {source : HexAWCoord}
  {e : Fin 3}
-- given
  (hs : source.color = .white) :
-- imply
  let q := (hexAWReturnPos source).add (hlha_negCoord (hexAWReturnPos (hexAWNeighbor source e))) q = hlhda_flatNeighbor ∨ HLHDAInwardDir q := by
-- proof
  apply StatMech.Universality.hlhda_normalized_neighbor_cases source hs e

/--
[hlhda_suffix_normalized_point](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_suffix_normalized_point_eq
  {ts : List ℤ}
  {t : ℤ}
  {us : List ℤ}
  {q : HexReturnCoord}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hsuf : ts.drop (hlhda_cutPos ts hleg) = t :: us)
  (hq : q ∈ hlha_edgeVertices HexReturnCoord.zero (hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t)) us) :
-- imply
  ∃ k, k ≤ ts.length ∧ q = (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 (hlhda_cutPos ts hleg))).add (hlha_negCoord (hexAWReturnPos (hlhc_prefixCoord ts hleg.1 k))) := by
-- proof
  apply StatMech.Universality.hlhda_suffix_normalized_point hleg hsuf hq

/--
[hlhda_suffix_flat_forces_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_suffix_flat_forces_terminal_eq
  {ts : List ℤ}
  {t : ℤ}
  {us : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hne : ts ≠ [])
  (hsuf : ts.drop (hlhda_cutPos ts hleg) = t :: us)
  (hflat : hlhda_flatNeighbor ∈ hlha_edgeVertices HexReturnCoord.zero (hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t)) us) :
-- imply
  us = [] := by
-- proof
  apply StatMech.Universality.hlhda_suffix_flat_forces_terminal hleg hne hsuf hflat

/--
[hlhda_inward_empty_hypotheses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_inward_empty_hypotheses_eq
  {d : HexReturnCoord}
-- given
  (hd : HLHDAInwardDir d) :
-- imply
  (hlha_edgeVertices HexReturnCoord.zero d []).Nodup ∧ (∀ q ∈ hlha_edgeVertices HexReturnCoord.zero d [], -2 ≤ hlhda_score q) ∧ hlhda_flatNeighbor ∉ hlha_edgeVertices HexReturnCoord.zero d [] := by
-- proof
  apply StatMech.Universality.hlhda_inward_empty_hypotheses d hd

/--
[hlhda_suffix_side_hypotheses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_suffix_side_hypotheses_eq
  {ts : List ℤ}
  {t : ℤ}
  {us : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hsuf : ts.drop (hlhda_cutPos ts hleg) = t :: us)
  (hnotFlat : hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t) ≠ hlhda_flatNeighbor) :
-- imply
  let d := hlha_negCoord ((hlhda_cutState ts hleg).dir.turn t) HLHDAInwardDir d ∧ (∀ u ∈ us, u = 1 ∨ u = -1) ∧ (hlha_edgeVertices HexReturnCoord.zero d us).Nodup ∧ (∀ q ∈ hlha_edgeVertices HexReturnCoord.zero d us, -2 ≤ hlhda_score q) ∧ hlhda_flatNeighbor ∉ hlha_edgeVertices HexReturnCoord.zero d us := by
-- proof
  apply StatMech.Universality.hlhda_suffix_side_hypotheses hleg hsuf hnotFlat

/--
[hlhda_suffixAugment_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_suffixAugment_isLegalSAW_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  (ofTurns hexAWStart 1 (hlhda_suffixAugment ts hleg)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlhda_suffixAugment_isLegalSAW ts hleg

/--
[hlhda_suffixAugment_halfSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_suffixAugment_halfSpace_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  HLHDLiteralHalfSpace (hlhda_suffixAugment ts hleg) (hlhda_suffixAugment_isLegalSAW ts hleg) := by
-- proof
  apply StatMech.Universality.hlhda_suffixAugment_halfSpace ts hleg

/--
[hlhda_suffixAugment_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_suffixAugment_length_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  (hlhda_suffixAugment ts hleg).length = (ts.drop (hlhda_cutPos ts hleg)).length + 2 := by
-- proof
  apply StatMech.Universality.hlhda_suffixAugment_length ts hleg

/--
[hlhda_suffixAugment_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_suffixAugment_spec_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  (ofTurns hexAWStart 1 (hlhda_suffixAugment ts hleg)).IsLegalSAW ∧ HLHDLiteralHalfSpace (hlhda_suffixAugment ts hleg) (hlhda_suffixAugment_isLegalSAW ts hleg) ∧ (hlhda_suffixAugment ts hleg).length = (ts.drop (hlhda_cutPos ts hleg)).length + 2 := by
-- proof
  apply StatMech.Universality.hlhda_suffixAugment_spec ts hleg

/--
[hlhda_entryTurn_injective_on_inward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_entryTurn_injective_on_inward_eq
  {d e : HexReturnCoord}
-- given
  (hd : HLHDAInwardDir d)
  (he : HLHDAInwardDir e)
  (h : hlhda_entryTurn d = hlhda_entryTurn e) :
-- imply
  d = e := by
-- proof
  apply StatMech.Universality.hlhda_entryTurn_injective_on_inward hd he h

/--
[hlhda_inward_ne_flat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_inward_ne_flat_eq
  {d : HexReturnCoord}
-- given
  (hd : HLHDAInwardDir d) :
-- imply
  d ≠ hlhda_flatNeighbor := by
-- proof
  apply StatMech.Universality.hlhda_inward_ne_flat hd

/--
[hlhda_coordRun_dir_pos_independent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_coordRun_dir_pos_independent_eq
  {p q d : HexReturnCoord}
  {ts : List ℤ} :
-- imply
  (hlhr_coordRun p d ts).dir = (hlhr_coordRun q d ts).dir := by
-- proof
  apply StatMech.Universality.hlhda_coordRun_dir_pos_independent p q d ts

/--
[hlhda_prefixAugment_eq_reverseCode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_prefixAugment_eq_reverseCode_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  hlhda_prefixAugment ts hleg = hlhda_reverseCode (ts.take (hlhda_cutPos ts hleg)) := by
-- proof
  apply StatMech.Universality.hlhda_prefixAugment_eq_reverseCode ts hleg

/--
[hlhda_reverseCode_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_reverseCode_injective_eq
  {xs ys : List ℤ}
-- given
  (hxlegal : ∀ t ∈ xs, t = 1 ∨ t = -1)
  (hylegal : ∀ t ∈ ys, t = 1 ∨ t = -1)
  (hxin : xs ≠ [] → HLHDAInwardDir (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base xs).dir)
  (hyin : ys ≠ [] → HLHDAInwardDir (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ys).dir)
  (heq : hlhda_reverseCode xs = hlhda_reverseCode ys) :
-- imply
  xs = ys := by
-- proof
  apply StatMech.Universality.hlhda_reverseCode_injective hxlegal hylegal hxin hyin heq

/--
[hlhda_suffixAugment_eq_forwardCode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_suffixAugment_eq_forwardCode_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  hlhda_suffixAugment ts hleg = hlhda_forwardCode (hlhda_cutState ts hleg).dir (ts.drop (hlhda_cutPos ts hleg)) := by
-- proof
  apply StatMech.Universality.hlhda_suffixAugment_eq_forwardCode ts hleg

/--
[hlhda_forwardEncodedDir_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_forwardEncodedDir_injective_eq
  {incoming : HexReturnCoord}
  {t u : ℤ}
-- given
  (hin : HLHDAInwardDir incoming)
  (ht : t = 1 ∨ t = -1)
  (hu : u = 1 ∨ u = -1)
  (hdt : hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor ∨ HLHDAInwardDir (hlha_negCoord (incoming.turn t)))
  (hdu : hlha_negCoord (incoming.turn u) = hlhda_flatNeighbor ∨ HLHDAInwardDir (hlha_negCoord (incoming.turn u)))
  (heq : hlhda_forwardEncodedDir incoming t = hlhda_forwardEncodedDir incoming u) :
-- imply
  t = u := by
-- proof
  apply StatMech.Universality.hlhda_forwardEncodedDir_injective incoming hin ht hu hdt hdu heq

/--
[hlhda_forwardCode_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_forwardCode_injective_eq
  {incoming : HexReturnCoord}
  {xs ys : List ℤ}
-- given
  (hin : HLHDAInwardDir incoming)
  (hxlegal : ∀ t ∈ xs, t = 1 ∨ t = -1)
  (hylegal : ∀ t ∈ ys, t = 1 ∨ t = -1)
  (hxdir : ∀ t us, xs = t :: us → hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor ∨ HLHDAInwardDir (hlha_negCoord (incoming.turn t)))
  (hydir : ∀ t us, ys = t :: us → hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor ∨ HLHDAInwardDir (hlha_negCoord (incoming.turn t)))
  (hxflat : ∀ t us, xs = t :: us → hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor → us = [])
  (hyflat : ∀ t us, ys = t :: us → hlha_negCoord (incoming.turn t) = hlhda_flatNeighbor → us = [])
  (heq : hlhda_forwardCode incoming xs = hlhda_forwardCode incoming ys) :
-- imply
  xs = ys := by
-- proof
  apply StatMech.Universality.hlhda_forwardCode_injective incoming hin hxlegal hylegal hxdir hydir hxflat hyflat heq

/--
[hlhda_augmentedPair_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_augmentedPair_length_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  (hlhda_augmentedPair ts hleg).1.length + (hlhda_augmentedPair ts hleg).2.length = ts.length + 4 := by
-- proof
  apply StatMech.Universality.hlhda_augmentedPair_length ts hleg

/--
[hlhda_augmentedPair_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_augmentedPair_injective_eq
  {xs ys : List ℤ}
-- given
  (hx : (ofTurns hexAWStart 1 xs).IsLegalSAW)
  (hy : (ofTurns hexAWStart 1 ys).IsLegalSAW)
  (heq : hlhda_augmentedPair xs hx = hlhda_augmentedPair ys hy) :
-- imply
  xs = ys := by
-- proof
  apply StatMech.Universality.hlhda_augmentedPair_injective hx hy heq

/--
[hlhda_decodePair_augmented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean)
-/
@[path]
private lemma hlhda_decodePair_augmented_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  hlhda_decodePair (hlhda_augmentedPair ts hleg) = ts := by
-- proof
  apply StatMech.Universality.hlhda_decodePair_augmented ts hleg


-- created on 2026-10-23
