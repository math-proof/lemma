import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
open StatMech StatMech.Universality


/--
[hexW2_exists_firstArgmax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_exists_firstArgmax_eq
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  ∃ cp, cp ≤ ts.length ∧ (∀ k ≤ ts.length, hexW2_partialDisp h0 ts k ≤ hexW2_partialDisp h0 ts cp) ∧ (∀ k, k < cp → hexW2_partialDisp h0 ts k < hexW2_partialDisp h0 ts cp) := by
-- proof
  apply StatMech.Universality.hexW2_exists_firstArgmax h0 ts

/--
[hexW2_cutPos_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_cutPos_le_eq
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  hexW2_cutPos h0 ts ≤ ts.length := by
-- proof
  apply StatMech.Universality.hexW2_cutPos_le h0 ts

/--
[hexW2_cutPos_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_cutPos_max_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (h0 : ℤ)
  (hk : k ≤ ts.length) :
-- imply
  hexW2_partialDisp h0 ts k ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts) := by
-- proof
  apply StatMech.Universality.hexW2_cutPos_max h0 ts k hk

/--
[hexW2_cutPos_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_cutPos_first_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (h0 : ℤ)
  (hk : k < hexW2_cutPos h0 ts) :
-- imply
  hexW2_partialDisp h0 ts k < hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts) := by
-- proof
  apply StatMech.Universality.hexW2_cutPos_first h0 ts k hk

/--
[hexW2_prefix_reachesWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_prefix_reachesWidth_eq
  {a : ℂ}
  {T : ℕ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hT : (T : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) :
-- imply
  hexWall3_ReachesWidth a h0 T (ts.take (hexW2_cutPos h0 ts)) := by
-- proof
  apply StatMech.Universality.hexW2_prefix_reachesWidth a h0 T ts hT

/--
[hexW2_prefix_reachesCutWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_prefix_reachesCutWidth_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hnn : 0 ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) :
-- imply
  hexWall3_ReachesWidth a h0 (hexW2_cutWidth h0 ts) (ts.take (hexW2_cutPos h0 ts)) := by
-- proof
  apply StatMech.Universality.hexW2_prefix_reachesCutWidth a h0 ts hnn

/--
[hexW2_cutWidth_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_cutWidth_pos_eq
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) :
-- imply
  0 < hexW2_cutWidth h0 ts := by
-- proof
  apply StatMech.Universality.hexW2_cutWidth_pos h0 ts hone

/--
[hexW2_prefix_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_prefix_legal_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hleg : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
-- imply
  (HexWalk.ofTurns a h0 (ts.take (hexW2_cutPos h0 ts))).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hexW2_prefix_legal a h0 ts hleg

/--
[hexW2_suffix_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_suffix_legal_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hleg : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
-- imply
  (HexWalk.ofTurns (hexDropMid a h0 ts (hexW2_cutPos h0 ts)) (h0 + (ts.take (hexW2_cutPos h0 ts)).sum) (ts.drop (hexW2_cutPos h0 ts))).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hexW2_suffix_legal a h0 ts hleg

/--
[hexW2_displacement_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_displacement_split_eq
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  hexInfra_stepReSum h0 ts = hexInfra_stepReSum h0 (ts.take (hexW2_cutPos h0 ts)) + hexInfra_stepReSum (hexInfra_headAccum h0 (ts.take (hexW2_cutPos h0 ts))) (ts.drop (hexW2_cutPos h0 ts)) := by
-- proof
  apply StatMech.Universality.hexW2_displacement_split h0 ts

/--
[hexW2_partialDisp_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_partialDisp_zero_eq
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  hexW2_partialDisp h0 ts 0 = (HexWalk.halfStep h0).re := by
-- proof
  apply StatMech.Universality.hexW2_partialDisp_zero h0 ts

/--
[hexW2_cutPos_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_cutPos_pos_eq
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) :
-- imply
  0 < hexW2_cutPos h0 ts := by
-- proof
  apply StatMech.Universality.hexW2_cutPos_pos h0 ts hone

/--
[hexW2_prefix_content_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_prefix_content_ne_eq
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) :
-- imply
  ts.take (hexW2_cutPos h0 ts) ≠ [] := by
-- proof
  apply StatMech.Universality.hexW2_prefix_content_ne h0 ts hone

/--
[hexW2_prefixBridge_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_prefixBridge_width_eq
  {ts : List ℤ}
  (hone)
-- given
  (h0 : ℤ) :
-- imply
  (hexW2_prefixBridge h0 ts hone).width = hexW2_cutWidth h0 ts := by
-- proof
  apply StatMech.Universality.hexW2_prefixBridge_width h0 ts

/--
[hexW2_prefixBridge_content](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_prefixBridge_content_eq
  {ts : List ℤ}
  (hone)
-- given
  (h0 : ℤ) :
-- imply
  (hexW2_prefixBridge h0 ts hone).content = ts.take (hexW2_cutPos h0 ts) := by
-- proof
  apply StatMech.Universality.hexW2_prefixBridge_content h0 ts

/--
[hexW2_prefixBridge_reaches_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_prefixBridge_reaches_legal_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts))
  (hleg : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
-- imply
  hexWall3_ReachesWidth a h0 (hexW2_prefixBridge h0 ts hone).width (hexW2_prefixBridge h0 ts hone).content ∧ (HexWalk.ofTurns a h0 (hexW2_prefixBridge h0 ts hone).content).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hexW2_prefixBridge_reaches_legal a h0 ts hone hleg

/--
[hexW2_prefixBridge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_prefixBridge_mem_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts))
  (hleg : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
-- imply
  hexWall3_mem a h0 (hexW2_prefixBridge h0 ts hone).width (hexW2_prefixBridge h0 ts hone).content := by
-- proof
  apply StatMech.Universality.hexW2_prefixBridge_mem a h0 ts hone hleg

/--
[hexW2_singleRight_partialDisp_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_singleRight_partialDisp_one_eq :
-- imply
  hexW2_partialDisp 0 [(-1 : ℤ)] 1 = (HexWalk.halfStep 0).re + 2 * (HexWalk.halfStep (-1)).re := by
-- proof
  apply StatMech.Universality.hexW2_singleRight_partialDisp_one

/--
[hexW2_singleRight_positiveWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_singleRight_positiveWidth_eq :
-- imply
  (1 : ℝ) ≤ hexW2_partialDisp 0 [(-1 : ℤ)] (hexW2_cutPos 0 [(-1 : ℤ)]) := by
-- proof
  apply StatMech.Universality.hexW2_singleRight_positiveWidth

/--
[hexW2_singleRight_cutPos_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_singleRight_cutPos_pos_eq :
-- imply
  0 < hexW2_cutPos 0 [(-1 : ℤ)] := by
-- proof
  apply StatMech.Universality.hexW2_singleRight_cutPos_pos

/--
[hexW2_singleRight_prefixBridge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean)
-/
@[path]
private lemma hexW2_singleRight_prefixBridge_mem_eq
  {a : ℂ} :
-- imply
  hexWall3_mem a 0 (hexW2_prefixBridge 0 [(-1 : ℤ)] hexW2_singleRight_positiveWidth).width (hexW2_prefixBridge 0 [(-1 : ℤ)] hexW2_singleRight_positiveWidth).content := by
-- proof
  apply StatMech.Universality.hexW2_singleRight_prefixBridge_mem a


-- created on 2026-10-23
