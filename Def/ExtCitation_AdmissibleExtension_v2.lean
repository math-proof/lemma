import Mathlib
import Def.ExtCitation_AdmissibleExtension
import Structure.ExtCitation_AdmissibleExtension_v2

set_option autoImplicit false

namespace ExtCitation

open ValuationSubring

variable (p : ℕ) [Fact p.Prime]
variable (V : Type) [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
  [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]


def ExtVanishingCts : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]
    (C : Submodule (ZMod p) V),
    IsAdmissibleExtensionCts p V C → SplitsGlobally C

def ExtVanishingCtsAll : Prop :=
  ∀ p : ℕ, (hp : p.Prime) → 3 ≤ p → @ExtVanishingCts p ⟨hp⟩

variable {p V} in

theorem extVanishingCts_of_extVanishing (h : ExtVanishing p) : ExtVanishingCts p :=
  fun V _ _ _ _ C hadm => h V C hadm.toIsAdmissibleExtension

end ExtCitation
