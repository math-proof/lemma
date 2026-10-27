import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma C1Sol.free_and_finrank_eq_of_span_eq_top [CommRing 𝒪] [IsDomain 𝒪] [CommRing A] [Nontrivial A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] [Module.Free 𝒪 A] [AddCommGroup M] [Module 𝒪 M] [Module A M] [IsScalarTower 𝒪 A M] [Module.Finite 𝒪 M] [Module.Free 𝒪 M] (d : ℕ) (f : Fin d → M) (hf : Submodule.span A (Set.range f) = ⊤) (hM : Module.finrank 𝒪 M = d * Module.finrank 𝒪 A) : Module.Free A M ∧ Module.finrank A M = d := by
  classical
  let φ : (Fin d → A) →ₗ[A] M := Fintype.linearCombination A f
  have hφ : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top]
    change LinearMap.range (Fintype.linearCombination A f) = ⊤
    rw [Fintype.range_linearCombination, hf]
  let ψ : (Fin d → A) →ₗ[𝒪] M := φ.restrictScalars 𝒪
  have hψ : Function.Surjective ψ := hφ
  have hrn := Submodule.rank_quotient_add_rank (LinearMap.ker ψ)
  rw [← Module.finrank_eq_rank 𝒪 ((Fin d → A) ⧸ LinearMap.ker ψ), (ψ.quotKerEquivOfSurjective hψ).finrank_eq, ← Module.finrank_eq_rank 𝒪 (Fin d → A), Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hM] at hrn
  have hker0 : Module.rank 𝒪 (LinearMap.ker ψ) = 0 := by
    have hlt : Module.rank 𝒪 (LinearMap.ker ψ) < Cardinal.aleph0 := by
      refine lt_of_le_of_lt ?_ (Cardinal.natCast_lt_aleph0 (n := d * Module.finrank 𝒪 A))
      calc
        _ ≤ ↑(d * Module.finrank 𝒪 A) + Module.rank 𝒪 (LinearMap.ker ψ) := self_le_add_left _ _
        _ = _ := hrn
    obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 hlt
    rw [hm] at hrn ⊢
    norm_cast at hrn ⊢
    omega
  have hker : LinearMap.ker ψ = ⊥ := Submodule.rank_eq_zero.mp hker0
  have hinj : Function.Injective φ := by
    have : Function.Injective ψ := LinearMap.ker_eq_bot.mp hker
    refine this
  let e : (Fin d → A) ≃ₗ[A] M := LinearEquiv.ofBijective φ ⟨hinj, hφ⟩
  exact ⟨Module.Free.of_equiv e, by rw [← e.finrank_eq, Module.finrank_fin_fun]⟩
/--
[Module_free_and_finrank_eq_of_finrank_eq_mul_of_finrank_residueField_tensor_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_free_and_finrank_eq_of_finrank_eq_mul_of_finrank_residueField_tensor_le.lean)
-/
@[path]
private lemma main
  [CommRing 𝒪] [IsDomain 𝒪] [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] [Module.Free 𝒪 A]
  [AddCommGroup M] [Module 𝒪 M] [Module A M] [IsScalarTower 𝒪 A M] [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
  (d : ℕ) (hd : Module.finrank (ResidueField A) (ResidueField A ⊗[A] M) ≤ d)
  (hM : Module.finrank 𝒪 M = d * Module.finrank 𝒪 A) :
  -- imply
  Module.Free A M ∧ Module.finrank A M = d := by
  -- proof
  classical
  let _ : Module.Finite A M := Module.Finite.of_restrictScalars_finite 𝒪 A M
  set n := Module.finrank (ResidueField A) (ResidueField A ⊗[A] M) with hn
  let b := Module.finBasis (ResidueField A) (ResidueField A ⊗[A] M)
  have hsurj1 : Function.Surjective (TensorProduct.mk A (ResidueField A) M 1) :=
    TensorProduct.mk_surjective A M (ResidueField A) IsLocalRing.residue_surjective
  choose f hf using fun i => hsurj1 (b i)
  have hspan : Submodule.span A (Set.range f) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis f b hf
  let g : Fin d → M := fun j => if h : (j : ℕ) < n then f ⟨j, h⟩ else 0
  have hsub : Set.range f ⊆ Set.range g := by
    rintro _ ⟨i, rfl⟩
    refine ⟨Fin.castLE hd i, ?_⟩
    simp [g]
  have hg : Submodule.span A (Set.range g) = ⊤ :=
    eq_top_iff.mpr (hspan ▸ Submodule.span_mono hsub)
  refine C1Sol.free_and_finrank_eq_of_span_eq_top d g hg hM


-- created on 2026-10-20
