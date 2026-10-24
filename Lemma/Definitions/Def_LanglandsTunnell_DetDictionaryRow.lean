import Lemma.Definitions.Def_TaylorWiles_Primes

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField Ideal FrobeniusDensity

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]

def DetDictionaryRow (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ 3 →
    ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (ratPrimeIdeal ℓ))
      (_ : Finite (𝓞 L ⧸ Q)),
      Q.inertia (L ≃ₐ[ℚ] L) = ⊥ →
      ((e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
        Matrix (Fin 2) (Fin 2) (ZMod 3)).det = (ℓ : ZMod 3)

end LanglandsTunnell
