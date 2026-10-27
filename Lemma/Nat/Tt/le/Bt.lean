import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.BNPair.Generalized.TypePreserving
open GeneralizedBNPair


namespace Definitions
end Definitions
namespace GeneralizedBNPair

/--
[Tt_le_Bt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Generalized/TypePreserving.lean)
-/
@[path]
private lemma Tt_le_Bt
  [Fintype B_idx]
  [DecidableEq B_idx]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {gbp : GeneralizedBNPair Gt M} :
-- imply
  gbp.Tt ≤ gbp.Bt := by
-- proof
  rwa [gbp.Tt_eq]

end GeneralizedBNPair

namespace GeneralizedBNPair

/--
[Bt_decomp_from_Gt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Generalized/TypePreserving.lean)
-/
@[path]
private lemma Bt_decomp_from_Gt
  [Fintype B_idx]
  [DecidableEq B_idx]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {gbp : GeneralizedBNPair Gt M} :
-- imply
  ∀ (x : Gt) (_ : x ∈ gbp.Bt), ∃ (t : Gt) (_ : t ∈ gbp.Tt) (g : Gt) (_ : g ∈ gbp.G) (_ : g ∈ gbp.Bt), x = t * g := by
-- proof
  intro x hx
  obtain ⟨t, ht, g, hg, hdecomp⟩ := gbp.Gt_decomp x
  refine ⟨t, ht, g, hg, ?_, hdecomp⟩
  have hg_eq : g = t⁻¹ * x := by
    have : t * g = x := hdecomp.symm
    rw [← this, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hg_eq]
  exact gbp.Bt.mul_mem (gbp.Bt.inv_mem (gbp.Tt_le_Bt ht)) hx

end GeneralizedBNPair

namespace GeneralizedBNPair

/--
[TypePreservingImpliesGlobal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Generalized/TypePreserving.lean)
-/
@[path]
private lemma TypePreservingImpliesGlobal
  [Fintype B_idx]
  [DecidableEq B_idx]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {gbp : GeneralizedBNPair Gt M}
  {g : Gt}
-- given
  (h : Gt)
  (hpres : gbp.PreservesTypesOnChamber g h) :
-- imply
  g ∈ gbp.G := by
-- proof
  obtain ⟨h', hh'G, hh'stab, hh'types⟩ :=
    gbp.strong_transitivity_for_types (h⁻¹ * g * h) hpres
  have hprod_in_G : h' * (h⁻¹ * g * h) ∈ gbp.G :=
    gbp.building_uniqueness_lemma _ hh'stab hh'types
  have hconj_in_G : h⁻¹ * g * h ∈ gbp.G := by
    have : h⁻¹ * g * h = h'⁻¹ * (h' * (h⁻¹ * g * h)) := by
      rw [← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact gbp.G.mul_mem (gbp.G.inv_mem hh'G) hprod_in_G
  have hg_eq : g = h * (h⁻¹ * g * h) * h⁻¹ := by
    simp [mul_assoc, mul_inv_cancel]
  rw [hg_eq]
  exact gbp.G_normal.conj_mem _ hconj_in_G h

end GeneralizedBNPair

namespace GeneralizedBNPair

/--
[LocalTypePreservingImpliesGlobal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Generalized/TypePreserving.lean)
-/
@[path]
private lemma LocalTypePreservingImpliesGlobal
  [Fintype B_idx]
  [DecidableEq B_idx]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {gbp : GeneralizedBNPair Gt M}
  {g : Gt}
-- given
  (h : Gt)
  (hpres : gbp.PreservesTypesOnChamber g h) :
-- imply
  g ∈ gbp.G :=
-- proof
  gbp.TypePreservingImpliesGlobal g h hpres

end GeneralizedBNPair


-- created on 2026-10-24
