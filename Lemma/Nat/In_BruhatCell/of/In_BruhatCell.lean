import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.BNPair.CellInvProof


/--
[BNPair.cell_inv_from_bnpair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellInvProof.lean)
-/
@[path]
private lemma cell_inv_from_bnpair_eq
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {w : M.Group}
  {g : G}
-- given
  (hg : g ∈ bp.bruhatCell w) :
-- imply
  g⁻¹ ∈ bp.bruhatCell w⁻¹ := by
-- proof
  apply BNPair.cell_inv_from_bnpair bp w g hg


-- created on 2026-10-24
