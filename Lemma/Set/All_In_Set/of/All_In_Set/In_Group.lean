import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.TransitiveAlcovesHelper
open Set AffineReflectionGroup
open scoped InnerProductSpace


namespace AffineReflectionGroup

/--
[group_maps_chamber_surj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TransitiveAlcovesHelper.lean)
-/
@[path]
lemma group_maps_chamber_surj
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {C D : W.arrangement.Chamber}
  {w : E ≃ᵃⁱ[ℝ] E}
-- given
  (hw : w ∈ W.group)
  (h_maps : ∀ x ∈ C.set, w x ∈ D.set) :
-- imply
  ∀ y : E, y ∈ C.set ↔ w y ∈ D.set := by
-- proof
  have hC_sub : C.set ⊆ (w : E → E) ⁻¹' D.set := fun x hx => h_maps x hx
  have hpreimage_compl : (w : E → E) ⁻¹' D.set ⊆ W.arrangement.complement := by
    intro x hx
    have hwx_compl := D.subset_complement hx
    rw [HyperplaneArrangement.complement] at hwx_compl ⊢
    simp only [Set.mem_diff, Set.mem_univ, true_and] at hwx_compl ⊢
    intro hx_union
    apply hwx_compl
    rw [HyperplaneArrangement.unionSet] at hx_union ⊢
    simp only [Set.mem_iUnion] at hx_union ⊢
    obtain ⟨ξ, hξ_mem, hx_carrier⟩ := hx_union
    obtain ⟨ξ', hξ'_mem, hξ'_char⟩ := W.stable w hw ξ hξ_mem
    exact ⟨ξ', hξ'_mem, (hξ'_char x).mpr hx_carrier⟩
  have hpreimage_conn : IsConnected ((w : E → E) ⁻¹' D.set) := by
    rw [show (w : E → E) ⁻¹' D.set = w.symm '' D.set from by
      ext x; constructor
      · intro hx; exact ⟨w x, hx, w.symm_apply_apply x⟩
      · intro ⟨d, hd, hxd⟩; rw [← hxd]; show w (w.symm d) ∈ D.set; rwa [w.apply_symm_apply]]
    exact D.isConnected.image (w.symm : E → E) w.symm.continuous.continuousOn
  have hpreimage_sub_C : (w : E → E) ⁻¹' D.set ⊆ C.set :=
    C.is_maximal _ hpreimage_compl hpreimage_conn hC_sub
  intro y
  constructor
  · exact fun hy => h_maps y hy
  · exact fun hy => hpreimage_sub_C hy

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[gallery_connectivity_axiom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TransitiveAlcovesHelper.lean)
-/
@[path]
lemma gallery_connectivity_axiom
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {C D : W.arrangement.Chamber} :
-- imply
  ∃ (reflections : List (E ≃ᵃⁱ[ℝ] E)), (∀ s ∈ reflections, s * s = 1 ∧ ∃ η ∈ W.arrangement.hyperplanes, ∀ y ∈ η.carrier, s y = y) ∧ (∀ y : E, y ∈ D.set ↔ reflections.prod y ∈ C.set) := by
-- proof
  suffices h : ∀ (n : ℕ) (C D : W.arrangement.Chamber),
    (W.separatingHyperplanes C D).ncard = n →
    ∃ (reflections : List (E ≃ᵃⁱ[ℝ] E)),
      (∀ s ∈ reflections, s * s = 1 ∧
        ∃ η ∈ W.arrangement.hyperplanes, ∀ y ∈ η.carrier, s y = y) ∧
      (∀ y : E, y ∈ D.set ↔ reflections.prod y ∈ C.set) from
    h _ C D rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro C D hCD
  by_cases heq : C.set = D.set
  ·
    refine ⟨[], fun s hs => absurd hs (List.not_mem_nil), fun y => ?_⟩
    simp only [List.prod_nil, AffineIsometryEquiv.coe_one, id]
    exact ⟨fun h => heq ▸ h, fun h => heq.symm ▸ h⟩
  ·
    obtain ⟨s, hs_group, η, hη_mem, _hη_wall, hs_fix, hs_inv, D',
      hs_maps, h_fewer⟩ :=
      wall_separation_step W C D heq
    have hs_iff : ∀ y, y ∈ C.set ↔ s y ∈ D'.set :=
      group_maps_chamber_surj W C D' s hs_group hs_maps
    have hs_iff_rev : ∀ z, z ∈ D'.set ↔ s z ∈ C.set := by
      intro z
      have h := hs_iff (s z)
      have hss : s (s z) = z := by
        have : (s * s : E ≃ᵃⁱ[ℝ] E) z = (1 : E ≃ᵃⁱ[ℝ] E) z := by rw [hs_inv]
        simp only [AffineIsometryEquiv.coe_mul, Function.comp,
          AffineIsometryEquiv.coe_one, id] at this
        exact this
      rwa [hss] at h
    have h_lt : (W.separatingHyperplanes D' D).ncard < n := by omega
    obtain ⟨refls', hrefls'_props, hrefls'_map⟩ := ih _ h_lt D' D rfl
    refine ⟨s :: refls', ?_, ?_⟩
    ·
      intro t ht
      simp only [List.mem_cons] at ht
      obtain rfl | ht := ht
      · exact ⟨hs_inv, η, hη_mem, hs_fix⟩
      · exact hrefls'_props t ht
    ·
      intro y
      simp only [List.prod_cons, AffineIsometryEquiv.coe_mul, Function.comp]
      constructor
      · intro hy
        exact (hs_iff_rev _).mp ((hrefls'_map y).mp hy)
      · intro hy
        exact (hrefls'_map y).mpr ((hs_iff_rev _).mpr hy)

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[list_prod_mem_group](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TransitiveAlcovesHelper.lean)
-/
@[path]
lemma list_prod_mem_group
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {G : Subgroup (E ≃ᵃⁱ[ℝ] E)}
  {l : List (E ≃ᵃⁱ[ℝ] E)}
-- given
  (hl : ∀ s ∈ l, s ∈ G) :
-- imply
  l.prod ∈ G := by
-- proof
  induction l with
  | nil => simp
  | cons s rest ih =>
    simp only [List.prod_cons]
    exact G.mul_mem (hl s List.mem_cons_self)
      (ih (fun t ht => hl t (List.mem_cons_of_mem s ht)))

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[involution_fixing_hyperplane_mem_group](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TransitiveAlcovesHelper.lean)
-/
@[path]
lemma involution_fixing_hyperplane_mem_group
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {s : E ≃ᵃⁱ[ℝ] E}
  {η : AffineHyperplane E}
-- given
  (hη : η ∈ W.arrangement.hyperplanes)
  (hs_inv : s * s = 1)
  (hs_fix : ∀ y ∈ η.carrier, s y = y) :
-- imply
  s ∈ W.group := by
-- proof
  by_cases hs_ne : s = 1
  ·
    subst hs_ne; exact W.group.one_mem
  ·
    obtain ⟨s', hs'_mem, hs'_fix, hs'_inv, hs'_ne⟩ := W.has_reflection η hη
    have heq : s = s' := reflection_unique s s' η hs_inv hs_fix hs'_inv hs'_fix hs_ne hs'_ne
    rw [heq]; exact hs'_mem

end AffineReflectionGroup

namespace AffineReflectionGroup

/--
[group_transitive_on_alcoves_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TransitiveAlcovesHelper.lean)
-/
@[path]
lemma group_transitive_on_alcoves_aux
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {W : AffineReflectionGroup E}
  {C D : W.Alcove} :
-- imply
  ∃ w ∈ W.group, ∀ y : E, y ∈ D.set ↔ (w : E ≃ᵃⁱ[ℝ] E) y ∈ C.set := by
-- proof
  obtain ⟨refls, hrefls_props, hrefls_map⟩ :=
    gallery_connectivity_axiom W C D
  have h_all_mem : ∀ s ∈ refls, s ∈ W.group := by
    intro s hs
    obtain ⟨hs_inv, η, hη_arr, hs_fix⟩ := hrefls_props s hs
    exact involution_fixing_hyperplane_mem_group W s η hη_arr hs_inv hs_fix
  exact ⟨refls.prod, list_prod_mem_group W.group refls h_all_mem, hrefls_map⟩

end AffineReflectionGroup


-- created on 2026-10-23
