import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.BNPair.CellMulFiniteProof.Part2
open CellMulFinite


/--
[setMul_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellMulFiniteProof.lean)
-/
@[path]
private lemma setMul_assoc_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {X Y Z : Set G} :
-- imply
  setMul (setMul X Y) Z = setMul X (setMul Y Z) := by
-- proof
  apply CellMulFinite.setMul_assoc X Y Z

/--
[setMul_mono_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellMulFiniteProof.lean)
-/
@[path]
private lemma setMul_mono_left_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {X₁ X₂ Y : Set G}
-- given
  (h : X₁ ⊆ X₂) :
-- imply
  setMul X₁ Y ⊆ setMul X₂ Y := by
-- proof
  apply CellMulFinite.setMul_mono_left h

/--
[setMul_mono_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellMulFiniteProof.lean)
-/
@[path]
private lemma setMul_mono_right_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {X Y₁ Y₂ : Set G}
-- given
  (h : Y₁ ⊆ Y₂) :
-- imply
  setMul X Y₁ ⊆ setMul X Y₂ := by
-- proof
  apply CellMulFinite.setMul_mono_right h

/--
[setMul_biUnion_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellMulFiniteProof.lean)
-/
@[path]
private lemma setMul_biUnion_left_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {A : ι → Set G}
  {B : Set G}
  {F : Finset ι} :
-- imply
  setMul (⋃ i ∈ F, A i) B = ⋃ i ∈ F, setMul (A i) B := by
-- proof
  apply CellMulFinite.setMul_biUnion_left A B F

/--
[bruhatCell_sub_setMul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellMulFiniteProof.lean)
-/
@[path]
private lemma bruhatCell_sub_setMul_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {w w' : M.Group} :
-- imply
  bp.bruhatCell (w * w') ⊆ setMul (bp.bruhatCell w) (bp.bruhatCell w') := by
-- proof
  apply CellMulFinite.bruhatCell_sub_setMul bp w w'

/--
[setMul_bruhatCell_simple_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellMulFiniteProof.lean)
-/
@[path]
private lemma setMul_bruhatCell_simple_subset_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp}
  {w : M.Group}
  {s : B_idx} :
-- imply
  setMul (bp.bruhatCell w) (bp.bruhatCell (M.toCoxeterSystem.simple s)) ⊆ ⋃ u ∈ setMul_bruhatCell_simple_finset bp ax w s, bp.bruhatCell u := by
-- proof
  apply CellMulFinite.setMul_bruhatCell_simple_subset bp ax w s

/--
[bruhatCell_mul_B_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellMulFiniteProof.lean)
-/
@[path]
private lemma bruhatCell_mul_B_right_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {w : M.Group}
  {g b : G}
-- given
  (hg : g ∈ bp.bruhatCell w)
  (hb : b ∈ bp.B) :
-- imply
  g * b ∈ bp.bruhatCell w := by
-- proof
  apply CellMulFinite.bruhatCell_mul_B_right bp hg hb

/--
[bruhatCell_one_sub_B](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellMulFiniteProof.lean)
-/
@[path]
private lemma bruhatCell_one_sub_B_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M} :
-- imply
  bp.bruhatCell 1 ⊆ (bp.B : Set G) := by
-- proof
  apply CellMulFinite.bruhatCell_one_sub_B bp

/--
[setMul_bruhatCell_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellMulFiniteProof.lean)
-/
@[path]
private lemma setMul_bruhatCell_one_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {w : M.Group} :
-- imply
  setMul (bp.bruhatCell w) (bp.bruhatCell 1) ⊆ bp.bruhatCell w := by
-- proof
  apply CellMulFinite.setMul_bruhatCell_one bp w

/--
[extend_finite_cover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellMulFiniteProof.lean)
-/
@[path]
private lemma extend_finite_cover_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp}
  {w' : M.Group}
  {s : B_idx}
  {w₀ : M.Group}
  {us : Finset M.Group}
-- given
  (h_IH : setMul (bp.bruhatCell w₀) (bp.bruhatCell w') ⊆ ⋃ u ∈ us, bp.bruhatCell u) :
-- imply
  ∃ (us' : Finset M.Group), setMul (bp.bruhatCell w₀) (bp.bruhatCell (w' * M.toCoxeterSystem.simple s)) ⊆ ⋃ u ∈ us', bp.bruhatCell u := by
-- proof
  apply CellMulFinite.extend_finite_cover bp ax w' s w₀ us h_IH

/--
[cell_mul_finite_from_bnpair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellMulFiniteProof.lean)
-/
@[path]
private lemma cell_mul_finite_from_bnpair_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp}
  {w w' : M.Group} :
-- imply
  ∃ (us : Finset M.Group), setMul (bp.bruhatCell w) (bp.bruhatCell w') ⊆ ⋃ u ∈ us, bp.bruhatCell u := by
-- proof
  apply CellMulFinite.cell_mul_finite_from_bnpair bp ax w w'


-- created on 2026-10-23
