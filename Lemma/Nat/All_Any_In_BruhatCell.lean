import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.CellCoverProof
import Lemma.Nat.In_BruhatCell1.of.In_B
import Lemma.Nat.NonemptyBruhatCell
import sympy.atlas.v1.Atlas.Buildings.code.BNPair.ParabolicDefs


namespace BNPair

/--
[cell_cover_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BruhatPropertiesWiring.lean)
-/
@[path]
private lemma cell_cover_unconditional
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {ax : BNPairAxioms bp} :
-- imply
  ∀ g : G, ∃ w : M.Group, g ∈ bp.bruhatCell w :=
-- proof
  CellCover.cell_cover_from_bnpair bp ax

end BNPair


-- created on 2026-10-24
