-- Carved from Lemma/Definitions/Def_GroupCohomology_GaloisSUnits.lean: instance decls only.
import Mathlib
import Def.FLTPrelim_Ramification
import Lemma.GroupCohomology.GaloisSUnits

set_option autoImplicit false

noncomputable section


namespace groupCohomology

open ValuationSubring

variable (S : Finset Nat.Primes)

instance instMulDistribMulActionGaloisSUnits :
    MulDistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ↥(galoisSUnits S) where
  smul σ x := ⟨σ • (x : (AlgebraicClosure ℚ)ˣ), smul_mem_galoisSUnits σ x.2⟩
  one_smul x := Subtype.ext (one_smul _ (x : (AlgebraicClosure ℚ)ˣ))
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ (x : (AlgebraicClosure ℚ)ˣ))
  smul_mul σ x y := Subtype.ext (smul_mul' σ (x : (AlgebraicClosure ℚ)ˣ) (y : (AlgebraicClosure ℚ)ˣ))
  smul_one σ := Subtype.ext (smul_one σ)

end groupCohomology

end
