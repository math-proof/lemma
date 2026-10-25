import Def.AutomorphicForm_HeckeEigensystem
import Def.LanglandsTunnell_ExplicitLift
import Def.ModularForm_EisensteinChiNegThree
import Def.FLTPrelim_Ramification
import Lemma.EllipticCurve.FrobeniusTrace
import Notation.LanglandsTunnell_IsAttached

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField AutomorphicForm IsDedekindDomain EisensteinWeightOne FLT.ExplicitLift

open scoped LanglandsTunnell_IsAttached

def IsAttachedExact (ρ : Γℚ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (π₀ : HeckeEigensystem ℚ (ℤ√(-2))) (T : Finset ℕ) : Prop :=
  ∀ p : Nat.Primes, (p : ℕ) ∉ T →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) →
      ∀ σ : Γℚ, A.IsFrobeniusAt σ (p : ℕ) →
        red (π₀.a ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p))
          = ((ρ σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
              Matrix (Fin 2) (Fin 2) (ZMod 3)).trace

def IsAttachedTwisted (ρ : Γℚ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (π₀ : HeckeEigensystem ℚ (ℤ√(-2))) (T : Finset ℕ) : Prop :=
  ∀ p : Nat.Primes, (p : ℕ) ∉ T →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) →
      ∀ σ : Γℚ, A.IsFrobeniusAt σ (p : ℕ) →
        red (π₀.a ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p))
          = ((chiNegThree (p : ℕ) : ℤ) : ZMod 3)
            * ((ρ σ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
                Matrix (Fin 2) (Fin 2) (ZMod 3)).trace

def IsAttachedUpToTwist (ρ : Γℚ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (π₀ : HeckeEigensystem ℚ (ℤ√(-2))) (T : Finset ℕ) : Prop :=
  IsAttachedExact ρ π₀ T ∨ IsAttachedTwisted ρ π₀ T

theorem isAttachedUpToTwist_one :
    IsAttachedUpToTwist 1 ⟨⊤, by simp, fun _ => 2, fun _ => 0⟩ ∅ :=
  Or.inl fun _ _ _ _ _ _ => by
    simp [Matrix.trace]
    exact map_ofNat red 2

end LanglandsTunnell
