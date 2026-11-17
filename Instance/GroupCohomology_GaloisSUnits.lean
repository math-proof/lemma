-- Carved from Lemma/Definitions/Def_GroupCohomology_GaloisSUnits.lean: instance decls only.
import Mathlib
import Def.GroupCohomology_GaloisSUnits

set_option autoImplicit false

noncomputable section


namespace groupCohomology

open ValuationSubring

variable (S : Finset Nat.Primes)

variable {S} in
private theorem smul_mem_galoisSUnits (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {x : (AlgebraicClosure ℚ)ˣ}
    (hx : x ∈ galoisSUnits S) : σ • x ∈ galoisSUnits S := by
  intro A hA
  have hA' : ∀ q ∈ S, ¬ (A.comap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)).LiesOverPrime ((q : Nat.Primes) : ℕ) :=
    fun q hq h => hA q hq ((A.liesOverPrime_comap_algEquiv_iff σ q).1 h)
  obtain ⟨h₁, h₂⟩ := hx _ hA'
  rw [ValuationSubring.mem_comap] at h₁ h₂
  refine ⟨h₁, ?_⟩
  rw [← smul_inv']
  exact h₂

instance instMulDistribMulActionGaloisSUnits :
    MulDistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ↥(galoisSUnits S) where
  smul σ x := ⟨σ • (x : (AlgebraicClosure ℚ)ˣ), smul_mem_galoisSUnits σ x.2⟩
  one_smul x := Subtype.ext (one_smul _ (x : (AlgebraicClosure ℚ)ˣ))
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ (x : (AlgebraicClosure ℚ)ˣ))
  smul_mul σ x y := Subtype.ext (smul_mul' σ (x : (AlgebraicClosure ℚ)ˣ) (y : (AlgebraicClosure ℚ)ˣ))
  smul_one σ := Subtype.ext (smul_one σ)

end groupCohomology

end
