module

public import Mathlib
public import Theorem.v1.Atlas.Buildings.code.BNPair.CellCoverProof
public import Theorem.Nat.In_BruhatCell1.of.In_B
public import Theorem.Nat.NonemptyBruhatCell
public import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2

public section


namespace BNPair

/--
[cell_cover_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/BruhatPropertiesWiring.lean)
-/
public theorem cell_cover_unconditional
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
