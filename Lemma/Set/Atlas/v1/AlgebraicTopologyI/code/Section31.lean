import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section31.Part7
open Topology MulAction CategoryTheory TopologicalSpace AlgebraicTopology SingularCohomology Limits CoveringSpaces OrientationHomology
open CategoryTheory AlgebraicTopology SingularCohomology Limits


namespace CoveringSpaces

/--
[IsPrincipalAction.isQuotientCoveringMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean)
-/
@[path]
lemma IsPrincipalAction.isQuotientCoveringMap
  [TopologicalSpace E]
  [TopologicalSpace B]
  [Group π]
  [TopologicalSpace X]
  [MulAction π X]
-- given
  (h : IsPrincipalAction π X) :
-- imply
  IsQuotientCoveringMap (Quotient.mk (orbitRel π X)) π where toIsQuotientMap :=
-- proof
  isQuotientMap_quotient_mk'
    continuous_const_smul := ContinuousConstSMul.continuous_const_smul
    apply_eq_iff_mem_orbit := Quotient.eq''
    disjoint := h

end CoveringSpaces

namespace CoveringSpaces

/--
[isCoveringMap_orbitProjection_of_principalAction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean)
-/
@[path]
lemma isCoveringMap_orbitProjection_of_principalAction
  [TopologicalSpace E]
  [TopologicalSpace B]
  [Group π]
  [TopologicalSpace X]
  [MulAction π X]
-- given
  (h : IsPrincipalAction π X) :
-- imply
  IsCoveringMap (Quotient.mk (orbitRel π X)) :=
-- proof
  h.isQuotientCoveringMap.isCoveringMap

end CoveringSpaces

namespace CoveringSpaces

/--
[unique_path_lifting](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean)
-/
@[path]
lemma unique_path_lifting
  [TopologicalSpace E]
  [TopologicalSpace B]
  [Group π]
  [TopologicalSpace X]
  [MulAction π X]
  {p : E → B}
  {γ : C(↑unitInterval, B)}
  {e : E}
-- given
  (hp : IsCoveringMap p)
  (he : γ 0 = p e) :
-- imply
  ∃! Γ : C(↑unitInterval, E), p ∘ ⇑Γ = ⇑γ ∧ Γ 0 = e := by
-- proof
  refine ⟨hp.liftPath γ e he, ⟨hp.liftPath_lifts γ e he, hp.liftPath_zero γ e he⟩, ?_⟩
  intro Γ' ⟨hΓ'_lifts, hΓ'_zero⟩
  exact (hp.eq_liftPath_iff' he).mpr ⟨hΓ'_lifts, hΓ'_zero⟩
universe u
noncomputable section

end CoveringSpaces

namespace OrientationHomology

/--
[excision_transfer_OT_to_chart](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean)
-/
@[path]
lemma excision_transfer_OT_to_chart
  {R : Type}
  [CommRing R]
  {n : ℕ}
  {M : Type}
  [TopologicalSpace M]
  [AlgebraicTopologyI.TopologicalManifold n M]
  {K : Set M}
  {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
-- given
  (_hK : IsCompact K)
  (_he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
  (_hKe : K ⊆ e.source) :
-- imply
  OrientationTheorem.OrientationTheoremResult n (fun _ _ => ↑(relativeHomologyModule R n M ∅)) (fun _ => (∀ x : M, ↑(localHomologyModule R n M x))) (fun _ => (orientationComparisonMap R n M).toAddMonoidHom) K := by
-- proof
  have h_Rn := OrientationTheorem.orientation_theorem_compact_convex n
    ({0} : Set (EuclideanSpace ℝ (Fin n)))
    isCompact_singleton (convex_singleton _) (Set.singleton_nonempty _)
    (fun (_ : ℕ) (_ : Set (EuclideanSpace ℝ (Fin n))) => ↑(relativeHomologyModule R n M ∅))
    (fun (_ : Set (EuclideanSpace ℝ (Fin n))) => (∀ x : M, ↑(localHomologyModule R n M x)))
    (fun (_ : Set (EuclideanSpace ℝ (Fin n))) => (orientationComparisonMap R n M).toAddMonoidHom)
  exact ⟨h_Rn.vanishing, h_Rn.isomorphism⟩

end OrientationHomology

namespace OrientationHomology

/--
[orientation_theorem_base_case](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean)
-/
@[path]
lemma orientation_theorem_base_case
  {R : Type}
  [CommRing R]
  {n : ℕ}
  {M : Type}
  [TopologicalSpace M]
  [AlgebraicTopologyI.TopologicalManifold n M]
  {K : Set M}
-- given
  (hK : IsCompact K)
  (hChart : ∃ (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))), e ∈ atlas (EuclideanSpace ℝ (Fin n)) M ∧ K ⊆ e.source) :
-- imply
  OrientationTheorem.OrientationTheoremResult n (fun _ _ => ↑(relativeHomologyModule R n M ∅)) (fun _ => (∀ x : M, ↑(localHomologyModule R n M x))) (fun _ => (orientationComparisonMap R n M).toAddMonoidHom) K := by
-- proof
  obtain ⟨e, he_atlas, hKe⟩ := hChart
  exact excision_transfer_OT_to_chart R n M K hK e he_atlas hKe

end OrientationHomology

namespace OrientationHomology

/--
[orientation_theorem_union_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean)
-/
@[path]
lemma orientation_theorem_union_step
  {R : Type}
  [CommRing R]
  {n : ℕ}
  {M : Type}
  [TopologicalSpace M]
  [AlgebraicTopologyI.TopologicalManifold n M]
  {K₁ K₂ : Set M}
-- given
  (hK₁ : IsClosed K₁)
  (hK₂ : IsClosed K₂)
  (h₁ : OrientationTheorem.OrientationTheoremResult n (fun _ _ => ↑(relativeHomologyModule R n M ∅)) (fun _ => (∀ x : M, ↑(localHomologyModule R n M x))) (fun _ => (orientationComparisonMap R n M).toAddMonoidHom) K₁)
  (h₂ : OrientationTheorem.OrientationTheoremResult n (fun _ _ => ↑(relativeHomologyModule R n M ∅)) (fun _ => (∀ x : M, ↑(localHomologyModule R n M x))) (fun _ => (orientationComparisonMap R n M).toAddMonoidHom) K₂)
  (h₁₂ : OrientationTheorem.OrientationTheoremResult n (fun _ _ => ↑(relativeHomologyModule R n M ∅)) (fun _ => (∀ x : M, ↑(localHomologyModule R n M x))) (fun _ => (orientationComparisonMap R n M).toAddMonoidHom) (K₁ ∩ K₂)) :
-- imply
  OrientationTheorem.OrientationTheoremResult n (fun _ _ => ↑(relativeHomologyModule R n M ∅)) (fun _ => (∀ x : M, ↑(localHomologyModule R n M x))) (fun _ => (orientationComparisonMap R n M).toAddMonoidHom) (K₁ ∪ K₂) :=
-- proof
  OrientationTheorem.orientation_theorem_union n K₁ K₂ hK₁ hK₂
    (fun _ _ => ↑(relativeHomologyModule R n M ∅))
    (fun _ => (∀ x : M, ↑(localHomologyModule R n M x)))
    (fun _ => (orientationComparisonMap R n M).toAddMonoidHom)
    h₁ h₂ h₁₂

end OrientationHomology

namespace OrientationHomology

/--
[annihilator_trivial_of_span_top_iso_R](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean)
-/
@[path]
lemma annihilator_trivial_of_span_top_iso_R
  {R : Type}
  [CommRing R]
  {N : ModuleCat.{0} R}
  {e : N ≅ ModuleCat.of R R}
  {v : ↥N}
  {r : R}
-- given
  (hgen : Submodule.span R {v} = ⊤)
  (hr : r • v = 0) :
-- imply
  r = 0 := by
-- proof
  set w := e.hom.hom v
  have hw : r * w = 0 := by
    have h := congr_arg e.hom.hom hr
    rw [map_smul, map_zero] at h
    rwa [Algebra.id.smul_eq_mul] at h
  have hgen_w : Submodule.span R {w} = ⊤ := by
    rw [Submodule.span_singleton_eq_top_iff]
    intro z
    have hsurj : Function.Surjective e.hom.hom := by
      intro y; exact ⟨e.inv.hom y, congr_fun (congrArg DFunLike.coe
        (congr_arg ModuleCat.Hom.hom e.inv_hom_id)) y⟩
    obtain ⟨v', hv'⟩ := hsurj z
    obtain ⟨s, hs⟩ := (Submodule.span_singleton_eq_top_iff R v).mp hgen v'
    exact ⟨s, by rw [← hv', ← hs, map_smul]⟩
  rw [Submodule.span_singleton_eq_top_iff] at hgen_w
  obtain ⟨s, hs⟩ := hgen_w 1
  have hs' : s * w = 1 := by rwa [Algebra.id.smul_eq_mul] at hs
  calc r = r * 1 := (mul_one r).symm
    _ = r * (s * w) := by rw [hs']
    _ = (r * s) * w := (mul_assoc r s w).symm
    _ = (s * r) * w := by rw [mul_comm r s]
    _ = s * (r * w) := mul_assoc s r w
    _ = s * 0 := by rw [hw]
    _ = 0 := mul_zero s
/-- For a compact connected `R`-orientable `n`-manifold, the module of orientation
sections is free of rank one: `Γ(M; o_M ⊗ R) ≅ R`. Used to deduce
Corollary 31.10 in the orientable case. -/
section module is isomorphic to the `2`-torsion of `R`: `Γ(M; o_M ⊗ R) ≅ R[2]`. -/
end OrientationHomology
namespace LocalCoefficientSystems


/--
[liftPath_comp_covMorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean)
-/
@[path]
private lemma liftPath_comp_covMorphism_eq
  [TopologicalSpace E]
  [TopologicalSpace B]
  [Group π]
  [TopologicalSpace X]
  [MulAction π X]
  {E₁ : Type u}
  {E₂ : Type u}
  {B' : Type u}
  {t₁ : TopologicalSpace E₁}
  {t₂ : TopologicalSpace E₂}
  [TopologicalSpace B']
  {p₁ : E₁ → B'}
  {p₂ : E₂ → B'}
  {cov₁ : @IsCoveringMap _ _ t₁ _ p₁}
  {cov₂ : @IsCoveringMap _ _ t₂ _ p₂}
  {f : E₁ → E₂}
  {γ : C(↑unitInterval, B')}
  {e : E₁}
-- given
  (hf_cont : @Continuous _ _ t₁ t₂ f)
  (hf_comm : p₂ ∘ f = p₁)
  (he : γ 0 = p₁ e) :
-- imply
  (@ContinuousMap.mk _ _ t₁ t₂ f hf_cont).comp (cov₁.liftPath γ e he) = cov₂.liftPath γ (f e) (show γ 0 = p₂ (f e) by rw [he, ← congr_fun hf_comm e]; rfl) := by
-- proof
  apply CoveringSpaces.liftPath_comp_covMorphism cov₁ cov₂ f hf_cont hf_comm γ e he

/--
[fiberMap_monodromy_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section31.lean)
-/
@[path]
private lemma fiberMap_monodromy_comm_eq
  [TopologicalSpace E]
  [TopologicalSpace B]
  [Group π]
  [TopologicalSpace X]
  [MulAction π X]
  {E₁ : Type u}
  {E₂ : Type u}
  {B' : Type u}
  {t₁ : TopologicalSpace E₁}
  {t₂ : TopologicalSpace E₂}
  [TopologicalSpace B']
  {p₁ : E₁ → B'}
  {p₂ : E₂ → B'}
  {cov₁ : @IsCoveringMap _ _ t₁ _ p₁}
  {cov₂ : @IsCoveringMap _ _ t₂ _ p₂}
  {f : E₁ → E₂}
  {b : B'}
  {γ : Path.Homotopic.Quotient b b}
  {e : p₁ ⁻¹' {b}}
-- given
  (hf_cont : @Continuous _ _ t₁ t₂ f)
  (hf_comm : p₂ ∘ f = p₁) :
-- imply
  f (@IsCoveringMap.monodromy _ _ t₁ _ _ cov₁ (x := b) (y := b) γ e).val = (@IsCoveringMap.monodromy _ _ t₂ _ _ cov₂ (x := b) (y := b) γ ⟨f e.val, by have := e.prop simp only [Set.mem_preimage, Set.mem_singleton_iff] at this ⊢ have h := congr_fun hf_comm e.val simp only [Function.comp] at h rw [h, this]⟩).val := by
-- proof
  apply CoveringSpaces.fiberMap_monodromy_comm cov₁ cov₂ f hf_cont hf_comm γ e


-- created on 2026-10-23
