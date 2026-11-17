import Mathlib
import Def.GroupCohomology_GaloisSUnits
import Instance.GroupCohomology_GaloisSUnits

set_option autoImplicit false

noncomputable section

namespace groupCohomology

open ValuationSubring

variable (S : Finset Nat.Primes)

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
