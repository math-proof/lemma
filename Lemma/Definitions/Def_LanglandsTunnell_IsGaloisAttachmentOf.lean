import Mathlib
import Lemma.Definitions.Def_LanglandsTunnell_OctahedralDatum
import Lemma.Definitions.Def_LanglandsTunnell_ExplicitLift
import Lemma.Definitions.Def_LanglandsTunnell_RealizationDictionary
import Lemma.Definitions.Def_EllipticCurve_FrobeniusTrace

set_option autoImplicit false

open AutomorphicForm FLT.TunnellOctahedralGlobalCarrier FLT.ExplicitLift
open scoped MatrixGroups

namespace FLT.TunnellOctahedralGlobalCarrier

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def IsGaloisAttachmentOf (ρ : Γℚ →* GL (Fin 2) (ZMod 3))
    (D : OctahedralGaloisDatum ℚ (ℤ√(-2))) (S : Finset ℕ) : Prop :=
  ∀ p : Nat.Primes, (p : ℕ) ∉ S →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) →
      ∀ σ : Γℚ, A.IsFrobeniusAt σ (p : ℕ) →
        red (D.attached.a (ratPrime p))
          = ((ρ σ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).trace

end FLT.TunnellOctahedralGlobalCarrier
