import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.CellCoverProof
open CellCover


namespace Definitions
end Definitions
/--
[B_mem_bruhatCell_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellCoverProof.lean)
-/
@[path]
private lemma B_mem_bruhatCell_one_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {b : G}
-- given
  (hb : b ∈ bp.B) :
-- imply
  b ∈ bp.bruhatCell 1 := by
-- proof
  apply CellCover.B_mem_bruhatCell_one bp hb

/--
[bruhatCell_mul_B_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellCoverProof.lean)
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
  apply CellCover.bruhatCell_mul_B_right bp hg hb

/--
[bruhatCell_mul_N_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellCoverProof.lean)
-/
@[path]
private lemma bruhatCell_mul_N_simple_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp}
  {w : M.Group}
  {g : G}
  {n : bp.N}
  {s : B_idx}
-- given
  (hg : g ∈ bp.bruhatCell w)
  (hn : bp.π n = M.toCoxeterSystem.simple s) :
-- imply
  ∃ u : M.Group, g * (n : G) ∈ bp.bruhatCell u := by
-- proof
  apply CellCover.bruhatCell_mul_N_simple bp ax hg hn

/--
[bruhatCell_mul_N](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellCoverProof.lean)
-/
@[path]
private lemma bruhatCell_mul_N_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp}
  {w : M.Group}
  {g : G}
  {n : bp.N}
-- given
  (hg : g ∈ bp.bruhatCell w) :
-- imply
  ∃ u : M.Group, g * (n : G) ∈ bp.bruhatCell u := by
-- proof
  apply CellCover.bruhatCell_mul_N bp ax hg n

/--
[cell_cover_from_bnpair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellCoverProof.lean)
-/
@[path]
private lemma cell_cover_from_bnpair_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp} :
-- imply
  ∀ g : G, ∃ w : M.Group, g ∈ bp.bruhatCell w := by
-- proof
  apply CellCover.cell_cover_from_bnpair bp ax


-- created on 2026-10-24
