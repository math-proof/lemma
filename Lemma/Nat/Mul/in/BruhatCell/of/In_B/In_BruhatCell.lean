import Mathlib
import sympy.Basic
import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Theorem.v1.Atlas.Buildings.code.BNPair.CellInvProof
import Lemma.Nat.In_BruhatCell.of.In_BruhatCell
import Lemma.Nat.In_BruhatCell1.of.In_B
import Theorem.v1.Atlas.Buildings.code.BNPair.CellCoverProof
open BNPair


namespace Definitions
end Definitions
namespace CellDisjoint

/--
[bruhatCell_mul_B_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellDisjointHelpers.lean)
-/
@[path]
private lemma bruhatCell_mul_B_left
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {w : M.Group}
  {g b : G}
-- given
  (hg : g ∈ bp.bruhatCell w)
  (hb : b ∈ bp.B) :
-- imply
  b * g ∈ bp.bruhatCell w := by
-- proof
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hg
  exact ⟨⟨b * b₁, bp.B.mul_mem hb hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, by rw [hg_eq]; group⟩

end CellDisjoint

namespace CellDisjoint

/--
[bruhatCell_mul_B_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellDisjointHelpers.lean)
-/
@[path]
private lemma bruhatCell_mul_B_right
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
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hg
  exact ⟨⟨b₁, hb₁⟩, n, ⟨b₂ * b, bp.B.mul_mem hb₂ hb⟩, hπ, by rw [hg_eq]; group⟩

end CellDisjoint

namespace CellDisjoint

/--
[N_lift_mem_bruhatCell_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellDisjointHelpers.lean)
-/
@[path]
private lemma N_lift_mem_bruhatCell_simple
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {n : bp.N}
  {s : B_idx}
-- given
  (hn : bp.π n = M.toCoxeterSystem.simple s) :
-- imply
  (n : G) ∈ bp.bruhatCell (M.toCoxeterSystem.simple s) :=
-- proof
  ⟨⟨1, bp.B.one_mem⟩, n, ⟨1, bp.B.one_mem⟩, hn, by simp⟩

end CellDisjoint


-- created on 2026-10-24
