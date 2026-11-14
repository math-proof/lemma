import Mathlib
import Def.FLTPrelim_Ramification
import Instance.GroupCohomology_GaloisSUnits

set_option autoImplicit false

noncomputable section

namespace ValuationSubring

lemma liesOverPrime_comap_algEquiv_iff (A : ValuationSubring (AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (q : ℕ) :
    (A.comap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)).LiesOverPrime q ↔ A.LiesOverPrime q := by
  simp only [LiesOverPrime, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_natCast]

end ValuationSubring

namespace groupCohomology

open ValuationSubring

variable (S : Finset Nat.Primes)

def galoisSUnits : Subgroup (AlgebraicClosure ℚ)ˣ where
  carrier := {x | ∀ A : ValuationSubring (AlgebraicClosure ℚ), (∀ q ∈ S, ¬ A.LiesOverPrime ((q : Nat.Primes) : ℕ)) →
    ((x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A ∧ ((x⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A}
  one_mem' A _ := by simp
  mul_mem' {x y} hx hy A hA := by
    obtain ⟨hx₁, hx₂⟩ := hx A hA
    obtain ⟨hy₁, hy₂⟩ := hy A hA
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact A.mul_mem _ _ hx₁ hy₁
    · rw [mul_inv_rev, Units.val_mul]; exact A.mul_mem _ _ hy₂ hx₂
  inv_mem' {x} hx A hA := by
    obtain ⟨hx₁, hx₂⟩ := hx A hA
    exact ⟨hx₂, by rwa [inv_inv]⟩

variable {S} in
lemma mem_galoisSUnits_iff (x : (AlgebraicClosure ℚ)ˣ) :
    x ∈ galoisSUnits S ↔ ∀ A : ValuationSubring (AlgebraicClosure ℚ), (∀ q ∈ S, ¬ A.LiesOverPrime ((q : Nat.Primes) : ℕ)) →
      ((x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A ∧ ((x⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A :=
  Iff.rfl

variable {S} in

lemma smul_mem_galoisSUnits (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {x : (AlgebraicClosure ℚ)ˣ}
    (hx : x ∈ galoisSUnits S) : σ • x ∈ galoisSUnits S := by
  intro A hA
  have hA' : ∀ q ∈ S, ¬ (A.comap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)).LiesOverPrime ((q : Nat.Primes) : ℕ) :=
    fun q hq h => hA q hq ((A.liesOverPrime_comap_algEquiv_iff σ q).1 h)
  obtain ⟨h₁, h₂⟩ := hx _ hA'
  rw [ValuationSubring.mem_comap] at h₁ h₂
  refine ⟨h₁, ?_⟩
  rw [← smul_inv']
  exact h₂

@[simp] lemma coe_smul_galoisSUnits (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥(galoisSUnits S)) :
    ((σ • x : ↥(galoisSUnits S)) : (AlgebraicClosure ℚ)ˣ) = σ • (x : (AlgebraicClosure ℚ)ˣ) := rfl

lemma coe_coe_smul_galoisSUnits (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥(galoisSUnits S)) :
    (((σ • x : ↥(galoisSUnits S)) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = σ ((x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) :=
  rfl

abbrev galoisSUnitsRep : Rep ℤ (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  Rep.ofMulDistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ↥(galoisSUnits S)

def galoisSUnitsToUnits : galoisSUnitsRep S →ₗ[ℤ] Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ) :=
  (MonoidHom.toAdditive (galoisSUnits S).subtype).toIntLinearMap

@[simp] lemma galoisSUnitsToUnits_apply (x : galoisSUnitsRep S) :
    galoisSUnitsToUnits S x = Additive.ofMul ((Additive.toMul x : ↥(galoisSUnits S)) : (AlgebraicClosure ℚ)ˣ) := rfl

lemma galoisSUnitsToUnits_injective : Function.Injective (galoisSUnitsToUnits S) :=
  fun _ _ h => Additive.toMul.injective (Subtype.ext (Additive.ofMul.injective h))

lemma galoisSUnitsToUnits_ρ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : galoisSUnitsRep S) :
    galoisSUnitsToUnits S ((galoisSUnitsRep S).ρ σ x) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ σ (galoisSUnitsToUnits S x) := rfl

end groupCohomology

end
