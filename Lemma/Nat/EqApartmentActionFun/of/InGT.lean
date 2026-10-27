import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.BNPair.TKernel.Part2


/--
[BNPair.T_acts_trivially_on_apartment](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/TKernel.lean)
-/
@[path]
private lemma BNPair.T_acts_trivially_on_apartment
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M}
  {n : bp.N}
  {w : M.Group}
-- given
  (hn : (n : G) ∈ bp.T) :
-- imply
  bp.apartmentActionFun n w = w := by
-- proof
  simp [BNPair.apartmentActionFun, (bp.π_ker n).mpr hn]

/--
[BNPair.T_subgroupOf_eq_ker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/TKernel.lean)
-/
@[path]
private lemma BNPair.T_subgroupOf_eq_ker
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M} :
-- imply
  bp.T.subgroupOf bp.N = bp.π.ker := by
-- proof
  ext ⟨x, hx⟩
  simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  exact (bp.π_ker ⟨x, hx⟩).symm

/--
[BNPair.quotientToW_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/TKernel.lean)
-/
@[path]
private lemma BNPair.quotientToW_injective
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M} :
-- imply
  Function.Injective (bp.quotientToW) := by
-- proof
  unfold BNPair.quotientToW
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [QuotientGroup.ker_lift]
  rw [← bp.T_subgroupOf_eq_ker]
  exact QuotientGroup.map_mk'_self _

/--
[BNPair.quotientToW_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/TKernel.lean)
-/
@[path]
private lemma BNPair.quotientToW_surjective
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M} :
-- imply
  Function.Surjective (bp.quotientToW) := by
-- proof
  intro w
  obtain ⟨n, hn⟩ := bp.π_surj w
  exact ⟨QuotientGroup.mk n, by simp [BNPair.quotientToW, hn]⟩

/--
[BNPair.quotientToW_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/TKernel.lean)
-/
@[path]
private lemma BNPair.quotientToW_bijective
  [Group G]
  {M : CoxeterMatrix B_idx}
  {bp : BNPair G M} :
-- imply
  Function.Bijective (bp.quotientToW) :=
-- proof
  ⟨bp.quotientToW_injective, bp.quotientToW_surjective⟩


-- created on 2026-10-24
