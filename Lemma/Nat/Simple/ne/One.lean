import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.BNPair.CellDisjointProof
open CellDisjoint
open BNPair


namespace Definitions
end Definitions
namespace CellDisjoint

/--
[simple_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellDisjointProof.lean)
-/
@[path]
private lemma simple_ne_one
  [Group G]
  {M : CoxeterMatrix B_idx}
  {cs : CoxeterSystem M M.Group}
  {s : B_idx} :
-- imply
  cs.simple s ≠ 1 := by
-- proof
  intro h; have := cs.length_simple s; rw [h, cs.length_one] at this; omega

end CellDisjoint

/--
[simple_inv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellDisjointProof.lean)
-/
@[path]
private lemma simple_inv_eq_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {cs : CoxeterSystem M M.Group}
  {s : B_idx} :
-- imply
  (cs.simple s)⁻¹ = cs.simple s := by
-- proof
  apply CellDisjoint.simple_inv_eq cs s

/--
[eq_one_of_mem_B_and_bruhatCell](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellDisjointProof.lean)
-/
@[path]
private lemma eq_one_of_mem_B_and_bruhatCell_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {g : G}
  {w : M.Group}
-- given
  (hg_B : g ∈ bp.B)
  (hg_w : g ∈ bp.bruhatCell w) :
-- imply
  w = 1 := by
-- proof
  apply CellDisjoint.eq_one_of_mem_B_and_bruhatCell bp hg_B hg_w

/--
[bruhatCell_one_sub_B'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellDisjointProof.lean)
-/
@[path]
private lemma bruhatCell_one_sub_B'_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {g : G}
-- given
  (hg : g ∈ bp.bruhatCell 1) :
-- imply
  g ∈ bp.B := by
-- proof
  apply CellDisjoint.bruhatCell_one_sub_B' bp hg

/--
[mul_simple_simple_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellDisjointProof.lean)
-/
@[path]
private lemma mul_simple_simple_self_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {cs : CoxeterSystem M M.Group}
  {w : M.Group}
  {s : B_idx} :
-- imply
  w * cs.simple s * cs.simple s = w := by
-- proof
  apply CellDisjoint.mul_simple_simple_self cs w s

/--
[cell_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellDisjointProof.lean)
-/
@[path]
private lemma cell_decomp_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {w : M.Group}
  {g : G}
  {s : B_idx}
-- given
  (hg : g ∈ bp.bruhatCell w)
  (_hlen : M.toCoxeterSystem.length (w * M.toCoxeterSystem.simple s) < M.toCoxeterSystem.length w) :
-- imply
  ∃ a ∈ bp.bruhatCell (w * M.toCoxeterSystem.simple s), ∃ b ∈ bp.bruhatCell (M.toCoxeterSystem.simple s), g = a * b := by
-- proof
  apply CellDisjoint.cell_decomp bp hg s _hlen

/--
[inv_mem_bruhatCell_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellDisjointProof.lean)
-/
@[path]
private lemma inv_mem_bruhatCell_simple_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {b : G}
  {s : B_idx}
-- given
  (hb : b ∈ bp.bruhatCell (M.toCoxeterSystem.simple s)) :
-- imply
  b⁻¹ ∈ bp.bruhatCell (M.toCoxeterSystem.simple s) := by
-- proof
  apply CellDisjoint.inv_mem_bruhatCell_simple bp hb

/--
[mem_setMul_of_mem_cells](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellDisjointProof.lean)
-/
@[path]
private lemma mem_setMul_of_mem_cells_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {w : M.Group}
  {s : B_idx}
  {x y : G}
-- given
  (hx : x ∈ bp.bruhatCell w)
  (hy : y ∈ bp.bruhatCell (M.toCoxeterSystem.simple s)) :
-- imply
  x * y ∈ setMul (bp.bruhatCell w) (bp.bruhatCell (M.toCoxeterSystem.simple s)) := by
-- proof
  apply CellDisjoint.mem_setMul_of_mem_cells bp hx hy

/--
[cell_disjoint_from_bnpair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellDisjointProof.lean)
-/
@[path]
private lemma cell_disjoint_from_bnpair_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp}
  {w w' : M.Group}
-- given
  (h : (bp.bruhatCell w ∩ bp.bruhatCell w').Nonempty) :
-- imply
  w = w' := by
-- proof
  apply CellDisjoint.cell_disjoint_from_bnpair bp ax w w' h


-- created on 2026-10-24
