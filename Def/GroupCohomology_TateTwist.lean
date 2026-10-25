import Mathlib

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace groupCohomology

section Conjugation

variable {k G : Type u} [CommRing k] [Group G] {A : Rep k G}

private noncomputable def pSum' (A : Rep k G) (g : G) (m : ℕ) : Module.End k A :=
  ∑ i ∈ Finset.range m, A.ρ (g ^ i)

private lemma pSum'_apply (g : G) (m : ℕ) (x : A) :
    pSum' A g m x = ∑ i ∈ Finset.range m, A.ρ (g ^ i) x :=
  LinearMap.sum_apply _ _ _

private lemma rho_pow_sub_one_apply_mem (t : G) (j : ℕ) (x : A) :
    A.ρ (t ^ j) x - x ∈ LinearMap.range (A.ρ t - 1) := by
  refine ⟨pSum' A t j x, ?_⟩
  have h : (A.ρ t - 1) * pSum' A t j = A.ρ (t ^ j) - 1 := by
    rw [map_pow, ← mul_geom_sum (A.ρ t) j]
    congr 1
    exact Finset.sum_congr rfl fun i _ => map_pow _ _ _
  calc (A.ρ t - 1) (pSum' A t j x) = ((A.ρ t - 1) * pSum' A t j) x := rfl
    _ = (A.ρ (t ^ j) - 1) x := by rw [h]
    _ = A.ρ (t ^ j) x - x := rfl

private lemma range_rho_sub_one_le_comap [Finite G] (t g : G)
    (h : g * t * g⁻¹ ∈ Subgroup.zpowers t) :
    LinearMap.range (A.ρ t - 1) ≤ (LinearMap.range (A.ρ t - 1)).comap (A.ρ g) := by
  obtain ⟨j, hj⟩ := (isOfFinOrder_of_finite t).mem_powers_iff_mem_zpowers.2 h
  replace hj : t ^ j = g * t * g⁻¹ := hj
  have hgt : g * t = t ^ j * g := by rw [hj]; group
  rintro _ ⟨x, rfl⟩
  simp only [Submodule.mem_comap]
  have key : A.ρ g ((A.ρ t - 1) x) = A.ρ (t ^ j) (A.ρ g x) - A.ρ g x := by
    have e1 : A.ρ g (A.ρ t x) = A.ρ (t ^ j) (A.ρ g x) := by
      rw [← Module.End.mul_apply, ← map_mul, hgt, map_mul, Module.End.mul_apply]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, e1]
  rw [key]
  exact rho_pow_sub_one_apply_mem t j (A.ρ g x)

end Conjugation

section TateOperator

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

noncomputable def frobeniusOnCoinvariants [Finite G] (t φ : G)
    (h : φ * t * φ⁻¹ ∈ Subgroup.zpowers t) :
    Module.End k (A ⧸ LinearMap.range (A.ρ t - 1)) :=
  Submodule.mapQ _ _ (A.ρ φ) (range_rho_sub_one_le_comap t φ h)

@[simp] lemma frobeniusOnCoinvariants_mk [Finite G] (t φ : G)
    (h : φ * t * φ⁻¹ ∈ Subgroup.zpowers t) (x : A) :
    frobeniusOnCoinvariants A t φ h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (A.ρ φ x) := rfl

noncomputable def evalAtGen (t : G) :
    cocycles₁ A →ₗ[k] A ⧸ LinearMap.range (A.ρ t - 1) :=
  (LinearMap.range (A.ρ t - 1)).mkQ ∘ₗ (LinearMap.proj t) ∘ₗ (cocycles₁ A).subtype

@[simp] lemma evalAtGen_apply (t : G) (f : cocycles₁ A) :
    evalAtGen A t f = Submodule.Quotient.mk (f t) := rfl

end TateOperator

end groupCohomology
