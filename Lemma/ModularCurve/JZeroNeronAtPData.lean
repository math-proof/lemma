import Mathlib
import Def.ModularCurve_JZeroNeronData
import Lemma.ModularCurve.MazurPrincipleCore
import Structure.ModularCurve_JZeroNeronAtPData

set_option autoImplicit false

noncomputable section

namespace ModularCurve


theorem mem_primesOf {M : ℕ} [NeZero M] (ℓ : Nat.Primes) : ℓ ∈ primesOf M ↔ (ℓ : ℕ) ∣ M := by
  have h1 := Finset.mem_subtype (s := M.primeFactors) (a := ℓ)
  refine h1.trans ?_
  rw [Nat.mem_primeFactors]
  exact ⟨fun h => h.2.1, fun h => ⟨ℓ.2, h, NeZero.ne _⟩⟩


def HasJZeroNeronAtPData (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronAtPData N q hqN A hA)

end ModularCurve

end
