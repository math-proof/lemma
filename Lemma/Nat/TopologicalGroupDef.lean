import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.Buildings.code.Building.ApplicationsToGroups.Part4
open ChamberComplex


namespace Definitions
end Definitions
/--
[TopologicalGroupDef.of_isTopologicalGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ApplicationsToGroups.lean)
-/
@[path]
private lemma TopologicalGroupDef.of_isTopologicalGroup
  {G : Type*}
  [TopologicalSpace G]
  [Group G]
  [IsTopologicalGroup G] :
-- imply
  TopologicalGroupDef G :=
-- proof
  ⟨continuous_mul, continuous_inv⟩

/--
[TopologicalGroupDef.toIsTopologicalGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ApplicationsToGroups.lean)
-/
@[path]
private lemma TopologicalGroupDef.toIsTopologicalGroup
  [TopologicalSpace G]
  [Group G]
-- given
  (h : TopologicalGroupDef G) :
-- imply
  IsTopologicalGroup G :=
-- proof
  { continuous_mul := h.mul_continuous
    continuous_inv := h.inv_continuous }
section PointwiseFixerProposition

/--
[pointwiseFixer_compact_open_prop](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ApplicationsToGroups.lean)
-/
@[path]
private lemma pointwiseFixer_compact_open_prop
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  {B : Subgroup G}
  {G_Y : Set G}
  {n : ℕ}
-- given
  (hB_compact : IsCompact (B : Set G))
  (hB_open : IsOpen (B : Set G))
  (hn : 0 < n)
  (h_conj : Fin n → G)
  (hG_Y_eq : G_Y = ⋂ i, (fun x => h_conj i * x * (h_conj i)⁻¹) '' (B : Set G)) :
-- imply
  IsOpen G_Y ∧ IsCompact G_Y := by
-- proof
  have conj_eq : ∀ (g : G),
    (fun x => g * x * g⁻¹) = (fun x => g * x) ∘ (fun x => x * g⁻¹) := by
    intro g; ext x; simp [Function.comp, mul_assoc]
  have isOpen_conj : ∀ g : G, IsOpen ((fun x => g * x * g⁻¹) '' (B : Set G)) := by
    intro g; rw [conj_eq, Set.image_comp]
    exact (isOpenMap_mul_left g) _ ((isOpenMap_mul_right g⁻¹) _ hB_open)
  have isClosed_conj : ∀ g : G, IsClosed ((fun x => g * x * g⁻¹) '' (B : Set G)) := by
    intro g; rw [conj_eq, Set.image_comp]
    exact (isClosedMap_mul_left g) _ ((isClosedMap_mul_right g⁻¹) _
      (Subgroup.isClosed_of_isOpen B hB_open))
  have isCompact_conj : ∀ g : G, IsCompact ((fun x => g * x * g⁻¹) '' (B : Set G)) := by
    intro g; rw [conj_eq, Set.image_comp]
    exact (hB_compact.image (continuous_mul_const g⁻¹)).image (continuous_const_mul g)
  rw [hG_Y_eq]
  refine ⟨isOpen_iInter_of_finite (fun i => isOpen_conj (h_conj i)),
    IsCompact.of_isClosed_subset
      (isCompact_conj (h_conj (⟨0, hn⟩ : Fin n)))
      (isClosed_iInter (fun i => isClosed_conj (h_conj i)))
      (Set.iInter_subset _ (⟨0, hn⟩ : Fin n))⟩
end PointwiseFixerProposition
section StrongTransitivity


-- created on 2026-10-24
