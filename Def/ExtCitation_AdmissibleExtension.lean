import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Def.FLTPrelim_Ramification
import Structure.ExtCitation_AdmissibleExtension

set_option autoImplicit false


namespace ExtCitation

open ValuationSubring

variable (p : ℕ) [Fact p.Prime]


variable (V : Type) [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
  [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]


variable {p V} in

def SplitsGlobally (C : Submodule (ZMod p) V) : Prop :=
  ∃ C' : Submodule (ZMod p) V,
    (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ C', σ • x ∈ C') ∧ IsCompl C C'

def ExtVanishing : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]
    (C : Submodule (ZMod p) V),
    IsAdmissibleExtension p V C → SplitsGlobally C

def ExtVanishingAll : Prop :=
  ∀ p : ℕ, (hp : p.Prime) → 3 ≤ p → @ExtVanishing p ⟨hp⟩

end ExtCitation
