import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexLiteralHWAugment
open StatMech StatMech.Universality


/--
[hlha_negCoord_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_negCoord_x_eq
  {p : HexReturnCoord} :
-- imply
  (hlha_negCoord p).x = -p.x := by
-- proof
  apply StatMech.Universality.hlha_negCoord_x p

/--
[hlha_negCoord_y](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_negCoord_y_eq
  {p : HexReturnCoord} :
-- imply
  (hlha_negCoord p).y = -p.y := by
-- proof
  apply StatMech.Universality.hlha_negCoord_y p

/--
[hlha_swapCoord_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_swapCoord_x_eq
  {p : HexReturnCoord} :
-- imply
  (hlha_swapCoord p).x = p.y := by
-- proof
  apply StatMech.Universality.hlha_swapCoord_x p

/--
[hlha_swapCoord_y](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_swapCoord_y_eq
  {p : HexReturnCoord} :
-- imply
  (hlha_swapCoord p).y = p.x := by
-- proof
  apply StatMech.Universality.hlha_swapCoord_y p

/--
[hlha_negCoord_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_negCoord_zero_eq :
-- imply
  hlha_negCoord HexReturnCoord.zero = HexReturnCoord.zero := by
-- proof
  apply StatMech.Universality.hlha_negCoord_zero

/--
[hlha_swapCoord_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_swapCoord_zero_eq :
-- imply
  hlha_swapCoord HexReturnCoord.zero = HexReturnCoord.zero := by
-- proof
  apply StatMech.Universality.hlha_swapCoord_zero

/--
[hlha_negCoord_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_negCoord_injective_eq :
-- imply
  Function.Injective hlha_negCoord := by
-- proof
  apply StatMech.Universality.hlha_negCoord_injective

/--
[hlha_swapCoord_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_swapCoord_injective_eq :
-- imply
  Function.Injective hlha_swapCoord := by
-- proof
  apply StatMech.Universality.hlha_swapCoord_injective

/--
[hlha_add_left_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_add_left_injective_eq
  {q : HexReturnCoord} :
-- imply
  Function.Injective q.add := by
-- proof
  apply StatMech.Universality.hlha_add_left_injective q

/--
[hlha_add_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_add_zero_eq
  {q : HexReturnCoord} :
-- imply
  q.add HexReturnCoord.zero = q := by
-- proof
  apply StatMech.Universality.hlha_add_zero q

/--
[hlha_zero_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_zero_add_eq
  {q : HexReturnCoord} :
-- imply
  HexReturnCoord.zero.add q = q := by
-- proof
  apply StatMech.Universality.hlha_zero_add q

/--
[hlha_negCoord_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_negCoord_add_eq
  {p q : HexReturnCoord} :
-- imply
  hlha_negCoord (p.add q) = (hlha_negCoord p).add (hlha_negCoord q) := by
-- proof
  apply StatMech.Universality.hlha_negCoord_add p q

/--
[hlha_swapCoord_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_swapCoord_add_eq
  {p q : HexReturnCoord} :
-- imply
  hlha_swapCoord (p.add q) = (hlha_swapCoord p).add (hlha_swapCoord q) := by
-- proof
  apply StatMech.Universality.hlha_swapCoord_add p q

/--
[hlha_negCoord_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_negCoord_turn_eq
  {d : HexReturnCoord}
  {t : ℤ}
-- given
  (ht : t = 1 ∨ t = -1) :
-- imply
  hlha_negCoord (d.turn t) = (hlha_negCoord d).turn t := by
-- proof
  apply StatMech.Universality.hlha_negCoord_turn d ht

/--
[hlha_swapCoord_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_swapCoord_turn_eq
  {d : HexReturnCoord}
  {t : ℤ}
-- given
  (ht : t = 1 ∨ t = -1) :
-- imply
  hlha_swapCoord (d.turn t) = (hlha_swapCoord d).turn (-t) := by
-- proof
  apply StatMech.Universality.hlha_swapCoord_turn d ht

/--
[hlha_coordVertices_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_coordVertices_length_eq
  {p d : HexReturnCoord}
  {ts : List ℤ} :
-- imply
  (hlha_coordVertices p d ts).length = ts.length + 1 := by
-- proof
  apply StatMech.Universality.hlha_coordVertices_length p d ts

/--
[hlha_edgeVertices_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_edgeVertices_length_eq
  {p d : HexReturnCoord}
  {ts : List ℤ} :
-- imply
  (hlha_edgeVertices p d ts).length = ts.length + 2 := by
-- proof
  apply StatMech.Universality.hlha_edgeVertices_length p d ts

/--
[hlha_edgeVertices_start_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_edgeVertices_start_mem_eq
  {p d : HexReturnCoord}
  {ts : List ℤ} :
-- imply
  p ∈ hlha_edgeVertices p d ts := by
-- proof
  apply StatMech.Universality.hlha_edgeVertices_start_mem p d ts

/--
[hlha_coordVertices_cons_eq_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_coordVertices_cons_eq_edge_eq
  {p d : HexReturnCoord}
  {t : ℤ}
  {ts : List ℤ} :
-- imply
  hlha_coordVertices p d (t :: ts) = hlha_edgeVertices p (d.turn t) ts := by
-- proof
  apply StatMech.Universality.hlha_coordVertices_cons_eq_edge p d t ts

/--
[hlha_coordVertices_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_coordVertices_neg_eq
  {p d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  hlha_coordVertices (hlha_negCoord p) (hlha_negCoord d) ts = (hlha_coordVertices p d ts).map hlha_negCoord := by
-- proof
  apply StatMech.Universality.hlha_coordVertices_neg p d ts hlegal

/--
[hlha_edgeVertices_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_edgeVertices_neg_eq
  {p d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  hlha_edgeVertices (hlha_negCoord p) (hlha_negCoord d) ts = (hlha_edgeVertices p d ts).map hlha_negCoord := by
-- proof
  apply StatMech.Universality.hlha_edgeVertices_neg p d ts hlegal

/--
[hlha_edgeVertices_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_edgeVertices_swap_eq
  {p d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  hlha_edgeVertices (hlha_swapCoord p) (hlha_swapCoord d) (hsc_negTurns ts) = (hlha_edgeVertices p d ts).map hlha_swapCoord := by
-- proof
  apply StatMech.Universality.hlha_edgeVertices_swap p d ts hlegal

/--
[hlha_edgeVertices_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_edgeVertices_translate_eq
  {q p d : HexReturnCoord}
  {ts : List ℤ} :
-- imply
  hlha_edgeVertices (q.add p) d ts = (hlha_edgeVertices p d ts).map (fun r => q.add r) := by
-- proof
  apply StatMech.Universality.hlha_edgeVertices_translate q p d ts

/--
[hlha_outerStep_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_outerStep_eq_eq :
-- imply
  hlha_outerStep = ⟨0, -1⟩ := by
-- proof
  apply StatMech.Universality.hlha_outerStep_eq

/--
[hlha_coordHeight_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_coordHeight_zero_eq :
-- imply
  HexReturnCoord.zero.x - HexReturnCoord.zero.y = 0 := by
-- proof
  apply StatMech.Universality.hlha_coordHeight_zero

/--
[hlha_outerStep_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_outerStep_height_eq :
-- imply
  hlha_outerStep.x - hlha_outerStep.y = 1 := by
-- proof
  apply StatMech.Universality.hlha_outerStep_height

/--
[hlha_normCoord_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_normCoord_height_eq
  {d p : HexReturnCoord} :
-- imply
  (hlha_normCoord d p).x - (hlha_normCoord d p).y = -(p.x - p.y) := by
-- proof
  apply StatMech.Universality.hlha_normCoord_height d p

/--
[hlha_normCoord_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_normCoord_injective_eq
  {d : HexReturnCoord} :
-- imply
  Function.Injective (hlha_normCoord d) := by
-- proof
  apply StatMech.Universality.hlha_normCoord_injective d

/--
[hlha_normDir_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_normDir_eq_eq
  {d : HexReturnCoord}
-- given
  (hd : HLHAAwayDir d) :
-- imply
  hlha_normCoord d d = hlha_outerStep.turn (hlha_cutTurn d) := by
-- proof
  apply StatMech.Universality.hlha_normDir_eq d hd

/--
[hlha_normTurns_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_normTurns_legal_eq
  {d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  ∀ t ∈ hlha_normTurns d ts, t = 1 ∨ t = -1 := by
-- proof
  apply StatMech.Universality.hlha_normTurns_legal d ts hlegal

/--
[hlha_augmentSide_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_augmentSide_legal_eq
  {d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  ∀ t ∈ hlha_augmentSide d ts, t = 1 ∨ t = -1 := by
-- proof
  apply StatMech.Universality.hlha_augmentSide_legal d ts hlegal

/--
[hlha_augmentSide_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_augmentSide_length_eq
  {d : HexReturnCoord}
  {ts : List ℤ} :
-- imply
  (hlha_augmentSide d ts).length = ts.length + 2 := by
-- proof
  apply StatMech.Universality.hlha_augmentSide_length d ts

/--
[hlha_normEdgeVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_normEdgeVertices_eq
  {d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  hlha_edgeVertices hlha_outerStep (hlha_normCoord d d) (hlha_normTurns d ts) = (hlha_edgeVertices HexReturnCoord.zero d ts).map (fun p => hlha_outerStep.add (hlha_normCoord d p)) := by
-- proof
  apply StatMech.Universality.hlha_normEdgeVertices d ts hlegal

/--
[hlha_coordVertices_augmentSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_coordVertices_augmentSide_eq
  {d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (hd : HLHAAwayDir d)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base (hlha_augmentSide d ts) = HexReturnCoord.zero :: (hlha_edgeVertices HexReturnCoord.zero d ts).map (fun p => hlha_outerStep.add (hlha_normCoord d p)) := by
-- proof
  apply StatMech.Universality.hlha_coordVertices_augmentSide d ts hd hlegal

/--
[hlha_augmented_vertex_height_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_augmented_vertex_height_pos_eq
  {d p : HexReturnCoord}
-- given
  (hp : p.x - p.y ≤ 0) :
-- imply
  0 < (hlha_outerStep.add (hlha_normCoord d p)).x - (hlha_outerStep.add (hlha_normCoord d p)).y := by
-- proof
  apply StatMech.Universality.hlha_augmented_vertex_height_pos d p hp

/--
[hlha_coordVertices_augmentSide_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_coordVertices_augmentSide_nodup_eq
  {d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (hd : HLHAAwayDir d)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hnodup : (hlha_edgeVertices HexReturnCoord.zero d ts).Nodup)
  (hbehind : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d ts, p.x - p.y ≤ 0) :
-- imply
  (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base (hlha_augmentSide d ts)).Nodup := by
-- proof
  apply StatMech.Universality.hlha_coordVertices_augmentSide_nodup d ts hd hlegal hnodup hbehind

/--
[hlha_verticesAux_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_verticesAux_coord_eq
  {p d : HexReturnCoord}
  {m s : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ)
  (hdir : halfStep h = d.value * s)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  verticesAux m h ts = (hlha_coordVertices p d ts).map (hlha_realizeCoord m s h p) := by
-- proof
  apply StatMech.Universality.hlha_verticesAux_coord p d m s h ts hdir hlegal

/--
[hlha_standard_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_standard_vertices_eq
  {ts : List ℤ}
-- given
  (hlegal : (ofTurns 0 0 ts).LegalTurns) :
-- imply
  (ofTurns 0 0 ts).vertices = (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).map hlha_standardRealize := by
-- proof
  apply StatMech.Universality.hlha_standard_vertices ts hlegal

/--
[hlha_value_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_value_injective_eq :
-- imply
  Function.Injective HexReturnCoord.value := by
-- proof
  apply StatMech.Universality.hlha_value_injective

/--
[hlha_standardRealize_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_standardRealize_injective_eq :
-- imply
  Function.Injective hlha_standardRealize := by
-- proof
  apply StatMech.Universality.hlha_standardRealize_injective

/--
[hlha_standard_isSAW_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_standard_isSAW_iff_eq
  {ts : List ℤ}
-- given
  (hlegal : (ofTurns 0 0 ts).LegalTurns) :
-- imply
  (ofTurns 0 0 ts).IsSAW ↔ (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).Nodup := by
-- proof
  apply StatMech.Universality.hlha_standard_isSAW_iff ts hlegal

/--
[hlha_coordRun_take_mem_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_coordRun_take_mem_tail_eq
  {p d : HexReturnCoord}
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hk : 0 < k)
  (hkle : k ≤ ts.length) :
-- imply
  (hlhr_coordRun p d (ts.take k)).pos ∈ (hlha_coordVertices p d ts).tail := by
-- proof
  apply StatMech.Universality.hlha_coordRun_take_mem_tail p d ts hk hkle

/--
[hlha_augmentSide_latticeHeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_augmentSide_latticeHeight_pos_eq
  {d : HexReturnCoord}
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hd : HLHAAwayDir d)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hbehind : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d ts, p.x - p.y ≤ 0)
  (hk : 0 < k)
  (hkle : k ≤ (hlha_augmentSide d ts).length) :
-- imply
  0 < hlhr_latticeHeight (hlha_augmentSide d ts) k := by
-- proof
  apply StatMech.Universality.hlha_augmentSide_latticeHeight_pos d ts hd hlegal hbehind hk hkle

/--
[hlha_augmentSide_halfSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_augmentSide_halfSpace_eq
  {d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (hd : HLHAAwayDir d)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hbehind : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d ts, p.x - p.y ≤ 0) :
-- imply
  HLHRLiteralHalfSpace 0 (hlha_augmentSide d ts) := by
-- proof
  apply StatMech.Universality.hlha_augmentSide_halfSpace d ts hd hlegal hbehind

/--
[hlha_augmentSide_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_augmentSide_isLegalSAW_eq
  {d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (hd : HLHAAwayDir d)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hnodup : (hlha_edgeVertices HexReturnCoord.zero d ts).Nodup)
  (hbehind : ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d ts, p.x - p.y ≤ 0) :
-- imply
  (ofTurns 0 0 (hlha_augmentSide d ts)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlha_augmentSide_isLegalSAW d ts hd hlegal hnodup hbehind

/--
[hlha_coordRun_direction_isUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_coordRun_direction_isUnit_eq
  {p d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (hd : d.IsUnit)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  (hlhr_coordRun p d ts).dir.IsUnit := by
-- proof
  apply StatMech.Universality.hlha_coordRun_direction_isUnit p d ts hd hlegal

/--
[hlha_mem_coordVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_mem_coordVertices_eq
  {p d : HexReturnCoord}
  {ts : List ℤ}
  {q : HexReturnCoord}
-- given
  (hq : q ∈ hlha_coordVertices p d ts) :
-- imply
  ∃ k, k ≤ ts.length ∧ q = (hlhr_coordRun p d (ts.take k)).pos := by
-- proof
  apply StatMech.Universality.hlha_mem_coordVertices p d ts hq

/--
[hlha_coordVertices_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_coordVertices_drop_eq
  {p d : HexReturnCoord}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (hcp : cp ≤ ts.length) :
-- imply
  let r := hlhr_coordRun p d (ts.take cp) hlha_coordVertices r.pos r.dir (ts.drop cp) = (hlha_coordVertices p d ts).drop cp := by
-- proof
  apply StatMech.Universality.hlha_coordVertices_drop p d ts cp hcp

/--
[hlha_cut_latticeHeight_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_cut_latticeHeight_max_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hlegal : (ofTurns 0 0 ts).LegalTurns)
  (hk : k ≤ ts.length) :
-- imply
  hlhr_latticeHeight ts k ≤ hlhr_latticeHeight ts (hexW2_cutPos 0 ts) := by
-- proof
  apply StatMech.Universality.hlha_cut_latticeHeight_max ts hlegal k hk

/--
[hlha_source_standard_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_source_standard_legal_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hlegal : (ofTurns a h0 ts).IsLegalSAW) :
-- imply
  (ofTurns 0 0 ts).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlha_source_standard_legal a h0 ts hlegal

/--
[hlha_source_coord_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_source_coord_nodup_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hlegal : (ofTurns a h0 ts).IsLegalSAW) :
-- imply
  (hlha_coordVertices HexReturnCoord.zero HexReturnCoord.base ts).Nodup := by
-- proof
  apply StatMech.Universality.hlha_source_coord_nodup a h0 ts hlegal

/--
[hlha_awayDir_of_isUnit_of_height_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_awayDir_of_isUnit_of_height_nonpos_eq
  {d : HexReturnCoord}
-- given
  (hu : d.IsUnit)
  (hh : d.x - d.y ≤ 0) :
-- imply
  HLHAAwayDir d := by
-- proof
  apply StatMech.Universality.hlha_awayDir_of_isUnit_of_height_nonpos d hu hh

/--
[hlha_emptyAugment_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_emptyAugment_isLegalSAW_eq :
-- imply
  (ofTurns 0 0 hlha_emptyAugment).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlha_emptyAugment_isLegalSAW

/--
[hlha_emptyAugment_halfSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_emptyAugment_halfSpace_eq :
-- imply
  HLHRLiteralHalfSpace 0 hlha_emptyAugment := by
-- proof
  apply StatMech.Universality.hlha_emptyAugment_halfSpace

/--
[hlha_emptyAugment_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_emptyAugment_length_eq :
-- imply
  hlha_emptyAugment.length = 1 := by
-- proof
  apply StatMech.Universality.hlha_emptyAugment_length

/--
[hlha_suffix_side_hypotheses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_suffix_side_hypotheses_eq
  {a : ℂ}
  {ts : List ℤ}
  {t : ℤ}
  {us : List ℤ}
-- given
  (h0 : ℤ)
  (hsource : (ofTurns a h0 ts).IsLegalSAW)
  (hsuffix : ts.drop (hexW2_cutPos 0 ts) = t :: us) :
-- imply
  let d := (hlha_cutState ts).dir.turn t HLHAAwayDir d ∧ (∀ u ∈ us, u = 1 ∨ u = -1) ∧ (hlha_edgeVertices HexReturnCoord.zero d us).Nodup ∧ ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d us, p.x - p.y ≤ 0 := by
-- proof
  apply StatMech.Universality.hlha_suffix_side_hypotheses a h0 ts hsource hsuffix

/--
[hlha_suffixAugment_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_suffixAugment_spec_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsource : (ofTurns a h0 ts).IsLegalSAW) :
-- imply
  (ofTurns 0 0 (hlha_suffixAugment ts)).IsLegalSAW ∧ HLHRLiteralHalfSpace 0 (hlha_suffixAugment ts) ∧ (hlha_suffixAugment ts).length = (ts.drop (hexW2_cutPos 0 ts)).length + 1 := by
-- proof
  apply StatMech.Universality.hlha_suffixAugment_spec a h0 ts hsource

/--
[hlha_negCoord_negCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_negCoord_negCoord_eq
  {p : HexReturnCoord} :
-- imply
  hlha_negCoord (hlha_negCoord p) = p := by
-- proof
  apply StatMech.Universality.hlha_negCoord_negCoord p

/--
[hlha_add_neg_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_add_neg_self_eq
  {p : HexReturnCoord} :
-- imply
  p.add (hlha_negCoord p) = HexReturnCoord.zero := by
-- proof
  apply StatMech.Universality.hlha_add_neg_self p

/--
[hlha_add_neg_cancel_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_add_neg_cancel_left_eq
  {p q : HexReturnCoord} :
-- imply
  (p.add q).add (hlha_negCoord q) = p := by
-- proof
  apply StatMech.Universality.hlha_add_neg_cancel_left p q

/--
[hlha_negTurn_back](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_negTurn_back_eq
  {d : HexReturnCoord}
  {t : ℤ}
-- given
  (ht : t = 1 ∨ t = -1) :
-- imply
  (hlha_negCoord (d.turn t)).turn (-t) = hlha_negCoord d := by
-- proof
  apply StatMech.Universality.hlha_negTurn_back d ht

/--
[hlha_loopReverse_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_loopReverse_cons_eq
  {t : ℤ}
  {ts : List ℤ} :
-- imply
  loopReverse (t :: ts) = loopReverse ts ++ [-t] := by
-- proof
  apply StatMech.Universality.hlha_loopReverse_cons t ts

/--
[hlha_coordRun_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_coordRun_append_eq
  {p d : HexReturnCoord}
  {xs ys : List ℤ} :
-- imply
  hlhr_coordRun p d (xs ++ ys) = let r := hlhr_coordRun p d xs hlhr_coordRun r.pos r.dir ys := by
-- proof
  apply StatMech.Universality.hlha_coordRun_append p d xs ys

/--
[hlha_edgeVertices_append_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_edgeVertices_append_single_eq
  {p d : HexReturnCoord}
  {ts : List ℤ}
  {t : ℤ} :
-- imply
  let r := hlhr_coordRun (p.add d) d ts hlha_edgeVertices p d (ts ++ [t]) = hlha_edgeVertices p d ts ++ [r.pos.add (r.dir.turn t)] := by
-- proof
  apply StatMech.Universality.hlha_edgeVertices_append_single p d ts t

/--
[hlha_edgeVertices_loopReverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_edgeVertices_loopReverse_eq
  {p d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  let r := hlhr_coordRun (p.add d) d ts hlha_edgeVertices r.pos (hlha_negCoord r.dir) (loopReverse ts) = (hlha_edgeVertices p d ts).reverse ∧ hlhr_coordRun (r.pos.add (hlha_negCoord r.dir)) (hlha_negCoord r.dir) (loopReverse ts) = ⟨p, hlha_negCoord d⟩ := by
-- proof
  apply StatMech.Universality.hlha_edgeVertices_loopReverse p d ts hlegal

/--
[hlha_negCoord_isUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_negCoord_isUnit_eq
  {d : HexReturnCoord}
-- given
  (hd : d.IsUnit) :
-- imply
  (hlha_negCoord d).IsUnit := by
-- proof
  apply StatMech.Universality.hlha_negCoord_isUnit hd

/--
[hlha_coordVertices_take](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_coordVertices_take_eq
  {p d : HexReturnCoord}
  {ts : List ℤ}
  {cp : ℕ} :
-- imply
  hlha_coordVertices p d (ts.take cp) = (hlha_coordVertices p d ts).take (cp + 1) := by
-- proof
  apply StatMech.Universality.hlha_coordVertices_take p d ts cp

/--
[hlha_prefix_side_hypotheses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_prefix_side_hypotheses_eq
  {a : ℂ}
  {ts : List ℤ}
  {t : ℤ}
  {us : List ℤ}
-- given
  (h0 : ℤ)
  (hsource : (ofTurns a h0 ts).IsLegalSAW)
  (hprefix : ts.take (hexW2_cutPos 0 ts) = t :: us) :
-- imply
  let d := hlha_negCoord (hlha_cutState ts).dir HLHAAwayDir d ∧ (∀ u ∈ loopReverse us, u = 1 ∨ u = -1) ∧ (hlha_edgeVertices HexReturnCoord.zero d (loopReverse us)).Nodup ∧ ∀ p ∈ hlha_edgeVertices HexReturnCoord.zero d (loopReverse us), p.x - p.y ≤ 0 := by
-- proof
  apply StatMech.Universality.hlha_prefix_side_hypotheses a h0 ts hsource hprefix

/--
[hlha_prefixAugment_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_prefixAugment_spec_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsource : (ofTurns a h0 ts).IsLegalSAW) :
-- imply
  (ofTurns 0 0 (hlha_prefixAugment ts)).IsLegalSAW ∧ HLHRLiteralHalfSpace 0 (hlha_prefixAugment ts) ∧ (hlha_prefixAugment ts).length = (ts.take (hexW2_cutPos 0 ts)).length + 1 := by
-- proof
  apply StatMech.Universality.hlha_prefixAugment_spec a h0 ts hsource

/--
[hlha_halfStep_coord_neg_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_halfStep_coord_neg_two_eq :
-- imply
  halfStep (-2) = (⟨-1, -1⟩ : HexReturnCoord).value * halfStep 0 := by
-- proof
  apply StatMech.Universality.hlha_halfStep_coord_neg_two

/--
[hlha_halfStep_coord_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_halfStep_coord_neg_one_eq :
-- imply
  halfStep (-1) = (⟨0, -1⟩ : HexReturnCoord).value * halfStep 0 := by
-- proof
  apply StatMech.Universality.hlha_halfStep_coord_neg_one

/--
[hlha_halfStep_coord_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_halfStep_coord_zero_eq :
-- imply
  halfStep 0 = (⟨1, 0⟩ : HexReturnCoord).value * halfStep 0 := by
-- proof
  apply StatMech.Universality.hlha_halfStep_coord_zero

/--
[hlha_halfStep_coord_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_halfStep_coord_one_eq :
-- imply
  halfStep 1 = (⟨1, 1⟩ : HexReturnCoord).value * halfStep 0 := by
-- proof
  apply StatMech.Universality.hlha_halfStep_coord_one

/--
[hlha_finalDirection_sum_mod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_finalDirection_sum_mod_eq
  {ts : List ℤ}
  {d : HexReturnCoord}
  {H : ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hfinal : (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = d)
  (hcoord : halfStep H = d.value * halfStep 0) :
-- imply
  (6 : ℤ) ∣ (ts.sum - H) := by
-- proof
  apply StatMech.Universality.hlha_finalDirection_sum_mod ts hlegal d H hfinal hcoord

/--
[hlha_reverseDir_mod_h1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_reverseDir_mod_h1_eq
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hdir : hlha_negCoord (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨1, 1⟩) :
-- imply
  (6 : ℤ) ∣ ts.sum - (-2) := by
-- proof
  apply StatMech.Universality.hlha_reverseDir_mod_h1 ts hlegal hdir

/--
[hlha_reverseDir_mod_h2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_reverseDir_mod_h2_eq
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hdir : hlha_negCoord (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨0, 1⟩) :
-- imply
  (6 : ℤ) ∣ ts.sum - (-1) := by
-- proof
  apply StatMech.Universality.hlha_reverseDir_mod_h2 ts hlegal hdir

/--
[hlha_reverseDir_mod_h3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_reverseDir_mod_h3_eq
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hdir : hlha_negCoord (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨-1, 0⟩) :
-- imply
  (6 : ℤ) ∣ ts.sum := by
-- proof
  apply StatMech.Universality.hlha_reverseDir_mod_h3 ts hlegal hdir

/--
[hlha_reverseDir_mod_h4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_reverseDir_mod_h4_eq
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (hdir : hlha_negCoord (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨-1, -1⟩) :
-- imply
  (6 : ℤ) ∣ ts.sum - 1 := by
-- proof
  apply StatMech.Universality.hlha_reverseDir_mod_h4 ts hlegal hdir

/--
[hlha_prefixAugment_eq_reverseAugment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_prefixAugment_eq_reverseAugment_eq
  {ts : List ℤ} :
-- imply
  hlha_prefixAugment ts = hlha_reverseAugment (ts.take (hexW2_cutPos 0 ts)) := by
-- proof
  apply StatMech.Universality.hlha_prefixAugment_eq_reverseAugment ts

/--
[hlha_normTurns_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_normTurns_injective_eq
  {d : HexReturnCoord} :
-- imply
  Function.Injective (hlha_normTurns d) := by
-- proof
  apply StatMech.Universality.hlha_normTurns_injective d

/--
[hlha_augmentSide_injective_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_augmentSide_injective_fixed_eq
  {d : HexReturnCoord} :
-- imply
  Function.Injective (hlha_augmentSide d) := by
-- proof
  apply StatMech.Universality.hlha_augmentSide_injective_fixed d

/--
[hlha_loopReverse_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_loopReverse_injective_eq :
-- imply
  Function.Injective loopReverse := by
-- proof
  apply StatMech.Universality.hlha_loopReverse_injective

/--
[hlha_reverseDir_mod_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_reverseDir_mod_cases_eq
  {ts : List ℤ}
-- given
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
  (haway : HLHAAwayDir (hlha_negCoord (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir)) :
-- imply
  (hlha_negCoord (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨1, 1⟩ ∧ (6 : ℤ) ∣ ts.sum - (-2)) ∨ (hlha_negCoord (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨0, 1⟩ ∧ (6 : ℤ) ∣ ts.sum - (-1)) ∨ (hlha_negCoord (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨-1, 0⟩ ∧ (6 : ℤ) ∣ ts.sum) ∨ (hlha_negCoord (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨-1, -1⟩ ∧ (6 : ℤ) ∣ ts.sum - 1) := by
-- proof
  apply StatMech.Universality.hlha_reverseDir_mod_cases ts hlegal haway

/--
[hlha_negTurns_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_negTurns_sum_eq
  {ts : List ℤ} :
-- imply
  (hsc_negTurns ts).sum = -ts.sum := by
-- proof
  apply StatMech.Universality.hlha_negTurns_sum ts

/--
[hlha_cross_h1_h4_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_cross_h1_h4_sum_eq
  {xs ys : List ℤ}
-- given
  (h : hlha_augmentSide ⟨1, 1⟩ (loopReverse xs) = hlha_augmentSide ⟨-1, -1⟩ (loopReverse ys)) :
-- imply
  xs.sum = -ys.sum := by
-- proof
  apply StatMech.Universality.hlha_cross_h1_h4_sum h

/--
[hlha_cross_h4_h1_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_cross_h4_h1_sum_eq
  {xs ys : List ℤ}
-- given
  (h : hlha_augmentSide ⟨-1, -1⟩ (loopReverse xs) = hlha_augmentSide ⟨1, 1⟩ (loopReverse ys)) :
-- imply
  xs.sum = -ys.sum := by
-- proof
  apply StatMech.Universality.hlha_cross_h4_h1_sum h

/--
[hlha_cross_h2_h3_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_cross_h2_h3_sum_eq
  {xs ys : List ℤ}
-- given
  (h : hlha_augmentSide ⟨0, 1⟩ (loopReverse xs) = hlha_augmentSide ⟨-1, 0⟩ (loopReverse ys)) :
-- imply
  xs.sum = -ys.sum := by
-- proof
  apply StatMech.Universality.hlha_cross_h2_h3_sum h

/--
[hlha_cross_h3_h2_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_cross_h3_h2_sum_eq
  {xs ys : List ℤ}
-- given
  (h : hlha_augmentSide ⟨-1, 0⟩ (loopReverse xs) = hlha_augmentSide ⟨0, 1⟩ (loopReverse ys)) :
-- imply
  xs.sum = -ys.sum := by
-- proof
  apply StatMech.Universality.hlha_cross_h3_h2_sum h

/--
[hlha_reverseAugment_injective_of_away](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_reverseAugment_injective_of_away_eq
  {xs ys : List ℤ}
-- given
  (hxlegal : ∀ t ∈ xs, t = 1 ∨ t = -1)
  (hylegal : ∀ t ∈ ys, t = 1 ∨ t = -1)
  (hxaway : xs ≠ [] → HLHAAwayDir (hlha_negCoord (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base xs).dir))
  (hyaway : ys ≠ [] → HLHAAwayDir (hlha_negCoord (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ys).dir))
  (heq : hlha_reverseAugment xs = hlha_reverseAugment ys) :
-- imply
  xs = ys := by
-- proof
  apply StatMech.Universality.hlha_reverseAugment_injective_of_away hxlegal hylegal hxaway hyaway heq

/--
[hlha_suffixAugment_eq_forwardAugment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_suffixAugment_eq_forwardAugment_eq
  {ts : List ℤ} :
-- imply
  hlha_suffixAugment ts = hlha_forwardAugment (hlha_cutState ts).dir (ts.drop (hexW2_cutPos 0 ts)) := by
-- proof
  apply StatMech.Universality.hlha_suffixAugment_eq_forwardAugment ts

/--
[hlha_sourceTurn_eq_of_cutTurn_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_sourceTurn_eq_of_cutTurn_eq_eq
  {incoming : HexReturnCoord}
  {t u : ℤ}
-- given
  (hi : incoming.IsUnit)
  (ht : t = 1 ∨ t = -1)
  (hu : u = 1 ∨ u = -1)
  (hdt : HLHAAwayDir (incoming.turn t))
  (hdu : HLHAAwayDir (incoming.turn u))
  (heq : hlha_cutTurn (incoming.turn t) = hlha_cutTurn (incoming.turn u)) :
-- imply
  t = u := by
-- proof
  apply StatMech.Universality.hlha_sourceTurn_eq_of_cutTurn_eq incoming hi ht hu hdt hdu heq

/--
[hlha_forwardAugment_injective_of_away](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_forwardAugment_injective_of_away_eq
  {incoming : HexReturnCoord}
  {xs ys : List ℤ}
-- given
  (hi : incoming.IsUnit)
  (hxlegal : ∀ t ∈ xs, t = 1 ∨ t = -1)
  (hylegal : ∀ t ∈ ys, t = 1 ∨ t = -1)
  (hxaway : ∀ t us, xs = t :: us → HLHAAwayDir (incoming.turn t))
  (hyaway : ∀ t us, ys = t :: us → HLHAAwayDir (incoming.turn t))
  (heq : hlha_forwardAugment incoming xs = hlha_forwardAugment incoming ys) :
-- imply
  xs = ys := by
-- proof
  apply StatMech.Universality.hlha_forwardAugment_injective_of_away incoming hi hxlegal hylegal hxaway hyaway heq

/--
[hlha_prefix_reverse_away](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_prefix_reverse_away_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsource : (ofTurns a h0 ts).IsLegalSAW)
  (hne : ts.take (hexW2_cutPos 0 ts) ≠ []) :
-- imply
  HLHAAwayDir (hlha_negCoord (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base (ts.take (hexW2_cutPos 0 ts))).dir) := by
-- proof
  apply StatMech.Universality.hlha_prefix_reverse_away a h0 ts hsource hne

/--
[hlha_suffix_forward_away](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_suffix_forward_away_eq
  {a : ℂ}
  {ts : List ℤ}
  {t : ℤ}
  {us : List ℤ}
-- given
  (h0 : ℤ)
  (hsource : (ofTurns a h0 ts).IsLegalSAW)
  (hs : ts.drop (hexW2_cutPos 0 ts) = t :: us) :
-- imply
  HLHAAwayDir ((hlha_cutState ts).dir.turn t) := by
-- proof
  apply StatMech.Universality.hlha_suffix_forward_away a h0 ts hsource hs

/--
[hlha_augmentedPair_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_augmentedPair_injective_eq
  {a : ℂ}
  {xs ys : List ℤ}
-- given
  (h0 : ℤ)
  (hx : (ofTurns a h0 xs).IsLegalSAW)
  (hy : (ofTurns a h0 ys).IsLegalSAW)
  (heq : hlha_augmentedPair xs = hlha_augmentedPair ys) :
-- imply
  xs = ys := by
-- proof
  apply StatMech.Universality.hlha_augmentedPair_injective a h0 hx hy heq

/--
[hlha_prefixAugment_cons_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_prefixAugment_cons_tail_eq
  {ts : List ℤ} :
-- imply
  (-1 : ℤ) :: (hlha_prefixAugment ts).tail = hlha_prefixAugment ts := by
-- proof
  apply StatMech.Universality.hlha_prefixAugment_cons_tail ts

/--
[hlha_suffixAugment_cons_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_suffixAugment_cons_tail_eq
  {ts : List ℤ} :
-- imply
  (-1 : ℤ) :: (hlha_suffixAugment ts).tail = hlha_suffixAugment ts := by
-- proof
  apply StatMech.Universality.hlha_suffixAugment_cons_tail ts

/--
[hlha_decodePair_augmented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_decodePair_augmented_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsource : (ofTurns a h0 ts).IsLegalSAW) :
-- imply
  hlha_decodePair a h0 (hlha_augmentedPair ts) = ts := by
-- proof
  apply StatMech.Universality.hlha_decodePair_augmented a h0 ts hsource

/--
[hlha_augmentedCore_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_augmentedCore_length_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsource : (ofTurns a h0 ts).IsLegalSAW) :
-- imply
  (hlha_prefixAugment ts).tail.length + (hlha_suffixAugment ts).tail.length = ts.length := by
-- proof
  apply StatMech.Universality.hlha_augmentedCore_length a h0 ts hsource

/--
[hlha_finite_partial_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean)
-/
@[path]
private lemma hlha_finite_partial_bound_eq
  {a : ℂ}
  {N : ℕ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 < x) :
-- imply
  ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤ (x ^ 2)⁻¹ * ((∑ s ∈ (hlha_augmentedTwoHalfData a h0 N).lowerImage, hhc_halfWeight x s) * (∑ s ∈ (hlha_augmentedTwoHalfData a h0 N).upperImage, hhc_halfWeight x s)) := by
-- proof
  apply StatMech.Universality.hlha_finite_partial_bound a h0 N hx


-- created on 2026-10-23
