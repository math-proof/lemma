import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.QCohProjective.Part2
open MvPolynomial QCohProjective


namespace QCohProjective

/--
[twist_twist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma twist_twist
  [Field k]
  {n : ℕ}
  {M : GradedModuleData k n}
  {d₁ d₂ : ℤ}
  {i : ℤ} :
-- imply
  ((M.twist d₁).twist d₂).component i = M.component (i + d₂ + d₁) := by
-- proof
  rfl

end QCohProjective

namespace QCohProjective

/--
[twist_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma twist_zero
  [Field k]
  {n : ℕ}
  {M : GradedModuleData k n}
  {i : ℤ} :
-- imply
  (M.twist 0).component i = M.component i := by
-- proof
  simp [GradedModuleData.twist]

end QCohProjective

namespace QCohProjective

/--
[twist_neg_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma twist_neg_cancel
  [Field k]
  {n : ℕ}
  {M : GradedModuleData k n}
  {d : ℤ}
  {i : ℤ} :
-- imply
  ((M.twist d).twist (-d)).component i = M.component i := by
-- proof
  simp [GradedModuleData.twist, add_assoc]

end QCohProjective

namespace QCohProjective

/--
[twist_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma twist_add
  [Field k]
  {n : ℕ}
  {M : GradedModuleData k n}
  {d₁ d₂ : ℤ}
  {i : ℤ} :
-- imply
  ((M.twist d₁).twist d₂).component i = (M.twist (d₁ + d₂)).component i := by
-- proof
  simp [GradedModuleData.twist, add_assoc, add_comm d₂ d₁]

end QCohProjective

namespace QCohProjective

/--
[torsion_iff_killed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma torsion_iff_killed
  [CommRing R]
  [IsDomain R]
  [AddCommGroup M]
  [Module R M]
  {m : M} :
-- imply
  m ∈ Submodule.torsion R M ↔ ∃ (r : R), r ≠ 0 ∧ r • m = 0 := by
-- proof
  rw [Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, ham⟩
    exact ⟨a, mem_nonZeroDivisors_iff_ne_zero.mp ha, ham⟩
  · rintro ⟨r, hr, hrm⟩
    exact ⟨⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr⟩, hrm⟩

end QCohProjective

namespace QCohProjective

/--
[torsion_module_iff_all_torsion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma torsion_module_iff_all_torsion
  [CommRing R]
  [IsDomain R]
  [AddCommGroup M]
  [Module R M] :
-- imply
  (∀ m : M, m ∈ Submodule.torsion R M) ↔ ∀ m : M, ∃ (r : R), r ≠ 0 ∧ r • m = 0 := by
-- proof
  constructor
  · intro h m
    have hm := h m
    rw [Submodule.mem_torsion_iff] at hm
    obtain ⟨⟨a, ha⟩, ham⟩ := hm
    exact ⟨a, mem_nonZeroDivisors_iff_ne_zero.mp ha, ham⟩
  · intro h m
    rw [Submodule.mem_torsion_iff]
    obtain ⟨r, hr, hrm⟩ := h m
    exact ⟨⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr⟩, hrm⟩

end QCohProjective

namespace QCohProjective

/--
[torsion_submodule_eq_set](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma torsion_submodule_eq_set
  [CommRing R]
  [IsDomain R]
  [AddCommGroup M]
  [Module R M] :
-- imply
  (Submodule.torsion R M : Set M) = {m : M | ∃ (r : R), r ≠ 0 ∧ r • m = 0} := by
-- proof
  ext m
  exact torsion_iff_killed m

end QCohProjective

namespace QCohProjective

/--
[serre_quotient_iso_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma serre_quotient_iso_criterion
  [CommRing R]
  [IsDomain R]
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup N]
  [Module R N]
  {f : M →ₗ[R] N} :
-- imply
  (∀ m : M, f m = 0 → m ∈ Submodule.torsion R M) ∧ (∀ n : N, ∃ (r : R), r ≠ 0 ∧ r • n ∈ LinearMap.range f) → (∀ m : M, f m ∈ Submodule.torsion R N → m ∈ Submodule.torsion R M) ∧ (∀ n : N, n ∈ Submodule.torsion R N ∨ ∃ (r : R), r ≠ 0 ∧ r • n ∈ LinearMap.range f) := by
-- proof
  intro ⟨h_ker, h_coker⟩
  constructor
  · intro m hfm
    rw [torsion_iff_killed] at hfm ⊢
    obtain ⟨r, hr, hrfm⟩ := hfm
    have hfr : f (r • m) = 0 := by rw [map_smul, hrfm]
    have hrm_tors := h_ker _ hfr
    rw [torsion_iff_killed] at hrm_tors
    obtain ⟨s, hs, hsrm⟩ := hrm_tors
    refine ⟨s * r, mul_ne_zero hs hr, ?_⟩
    rw [mul_smul, hsrm]
  · intro n
    obtain ⟨r, hr, hrn⟩ := h_coker n
    exact Or.inr ⟨r, hr, hrn⟩

end QCohProjective

namespace QCohProjective

/--
[tilde_proj_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma tilde_proj_exact
  [CommRing R]
  [AddCommGroup M₁]
  [Module R M₁]
  [AddCommGroup M₂]
  [Module R M₂]
  [AddCommGroup M₃]
  [Module R M₃]
  {f : M₁ →ₗ[R] M₂}
  {g : M₂ →ₗ[R] M₃}
  {S : Submonoid R}
-- given
  (hex : Function.Exact f g) :
-- imply
  Function.Exact (LocalizedModule.map S f) (LocalizedModule.map S g) :=
-- proof
  LocalizedModule.map_exact S f g hex

end QCohProjective

namespace QCohProjective

/--
[shiftedModule_degree_zero_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma shiftedModule_degree_zero_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {M : GradedModuleData k n}
  {d : ℤ} :
-- imply
  (M.twist d).component 0 = M.component d := by
-- proof
  simp [GradedModuleData.twist]

end QCohProjective

namespace QCohProjective

/--
[globalSections_Od_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma globalSections_Od_finrank
  {k : Type*}
  [Field k]
  {n d : ℕ} :
-- imply
  Module.finrank k (homogeneousSubmodule (Fin (n + 1)) k d) = (n + d).choose n := by
-- proof
  rw [_root_.homogeneousSubmodule_finrank]
  have h1 : n + 1 + d - 1 = n + d := by omega
  rw [h1, Nat.choose_symm_add.symm]

end QCohProjective

namespace QCohProjective

/--
[homogeneous_component_finiteDim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma homogeneous_component_finiteDim
  {k : Type*}
  [Field k]
  {n d : ℕ} :
-- imply
  Module.Finite k (homogeneousSubmodule (Fin n) k d) :=
-- proof
  _root_.homogeneousSubmodule_finiteDimensional k n d

end QCohProjective

namespace QCohProjective

/--
[surjective_mapQ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma surjective_mapQ
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup N]
  [Module R N]
  {f : M →ₗ[R] N}
  {p : Submodule R M}
  {q : Submodule R N}
-- given
  (hf : Function.Surjective f)
  (hpq : p ≤ Submodule.comap f q) :
-- imply
  Function.Surjective (p.mapQ q f hpq) := by
-- proof
  intro y
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective q y
  obtain ⟨m, rfl⟩ := hf n
  exact ⟨Submodule.Quotient.mk m, rfl⟩

end QCohProjective

namespace QCohProjective

/--
[localization_preserves_surjectivity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma localization_preserves_surjectivity
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup N]
  [Module R N]
  {f : M →ₗ[R] N}
  [AddCommGroup P]
  [Module R P]
  {g : N →ₗ[R] P}
-- given
  (hf : Function.Surjective f)
  (hg : Function.Surjective g) :
-- imply
  Function.Surjective (g.comp f) :=
-- proof
  hg.comp hf

end QCohProjective

namespace QCohProjective

/--
[fg_module_quotient_of_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma fg_module_quotient_of_free
  {R : Type*}
  [CommRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M] :
-- imply
  ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), Function.Surjective f := by
-- proof
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  refine ⟨n, (Finsupp.linearCombination R s).comp
    (Finsupp.linearEquivFunOnFinite R R (Fin n)).symm.toLinearMap, ?_⟩
  intro m
  have hm : m ∈ Submodule.span R (Set.range s) := hs ▸ Submodule.mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hm
  obtain ⟨c, rfl⟩ := hm
  exact ⟨Finsupp.linearEquivFunOnFinite R R (Fin n) c, by
    simp [LinearMap.comp_apply, LinearEquiv.symm_apply_apply,
      Finsupp.linearCombination_apply]⟩

end QCohProjective

namespace QCohProjective

/--
[torsion_killed_by_localization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma torsion_killed_by_localization
  [CommRing R]
  [IsDomain R]
  [AddCommGroup M]
  [Module R M]
  {S : Submonoid R}
  {m : M}
-- given
  (hm : m ∈ Submodule.torsion R M)
  (hS : nonZeroDivisors R ≤ S) :
-- imply
  ∃ (t : S), (t : R) • m = 0 := by
-- proof
  rw [Submodule.mem_torsion_iff] at hm
  obtain ⟨⟨a, ha⟩, ham⟩ := hm
  exact ⟨⟨a, hS ha⟩, ham⟩

end QCohProjective

namespace QCohProjective

/--
[torsion_module_localization_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma torsion_module_localization_trivial
  [CommRing R]
  [IsDomain R]
  [AddCommGroup M]
  [Module R M]
  {m : M}
-- given
  (htors : ∀ m : M, m ∈ Submodule.torsion R M) :
-- imply
  ∃ (r : R), r ≠ 0 ∧ r • m = 0 :=
-- proof
(torsion_module_iff_all_torsion.mp htors) m

end QCohProjective

namespace QCohProjective

/--
[double_twist_eq_twist_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma double_twist_eq_twist_add
  [Field k]
  {n : ℕ}
  {M : GradedModuleData k n}
  {d₁ d₂ : ℤ}
  {i : ℤ} :
-- imply
  ((M.twist d₁).twist d₂).component i = (M.twist (d₁ + d₂)).component i := by
-- proof
  simp [GradedModuleData.twist, add_assoc, add_comm d₂ d₁]

end QCohProjective

namespace QCohProjective

/--
[twist_tensor_product_correspondence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma twist_tensor_product_correspondence
  [Field k]
  {n : ℕ}
  {M : GradedModuleData k n}
  {d₁ d₂ : ℤ}
  {i : ℤ} :
-- imply
  ((M.twist d₁).twist d₂).component i = (M.twist (d₁ + d₂)).component i :=
-- proof
  double_twist_eq_twist_add M d₁ d₂ i

end QCohProjective

namespace QCohProjective

/--
[twist_zero_structure_sheaf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma twist_zero_structure_sheaf
  [Field k]
  {n : ℕ}
  {M : GradedModuleData k n}
  {i : ℤ} :
-- imply
  (M.twist 0).component i = M.component i := by
-- proof
  simp [GradedModuleData.twist]

end QCohProjective

namespace QCohProjective

/--
[globalSections_twisted_structure_sheaf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma globalSections_twisted_structure_sheaf
  [Field k]
  {n : ℕ}
  {M : GradedModuleData k n}
  {d : ℤ} :
-- imply
  (M.twist d).component 0 = M.component d := by
-- proof
  simp [GradedModuleData.twist]

end QCohProjective

namespace QCohProjective

/--
[globalSections_Od_dimension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma globalSections_Od_dimension
  {k : Type*}
  [Field k]
  {n d : ℕ} :
-- imply
  Module.finrank k (gradedComponent k n d) = (n + d).choose n := by
-- proof
  unfold gradedComponent
  exact globalSections_Od_finrank k n d

end QCohProjective

namespace QCohProjective

/--
[hilbert_function_via_Od](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma hilbert_function_via_Od
  {k : Type*}
  [Field k]
  {n d : ℕ} :
-- imply
  Module.finrank k (gradedComponent k n d) = (n + d).choose d := by
-- proof
  rwa [globalSections_Od_dimension]

end QCohProjective

namespace QCohProjective

/--
[gradedComponent_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohProjective.lean)
-/
@[path]
lemma gradedComponent_mono
  {k : Type*}
  [Field k]
  {n d : ℕ} :
-- imply
  Module.finrank k (gradedComponent k n d) ≤ Module.finrank k (gradedComponent k n (d + 1)) := by
-- proof
  simp only [globalSections_Od_dimension]
  exact Nat.choose_le_choose n (by omega)
end QCohProjective



-- created on 2026-10-23
