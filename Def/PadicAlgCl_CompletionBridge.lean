module

public import Mathlib
public import Def.FLTPrelim_Ramification
public import Abbrev.GaloisRep_CompletionBridge

@[expose] public section

set_option autoImplicit false

open scoped NNReal Pointwise

variable (q : ℕ) [Fact q.Prime]

noncomputable def padicEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl q :=
  IsAlgClosed.lift

noncomputable def padicPlace : ValuationSubring (AlgebraicClosure ℚ) :=
  (padicIntegers q).comap (padicEmbedding q).toRingHom

section Galois

noncomputable def localGaloisToGlobal :
    (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := PadicAlgCl q) (AlgebraicClosure ℚ)).comp
    (MonoidHom.mk' (fun τ => τ.restrictScalars ℚ) (fun _ _ => rfl))

end Galois

end
