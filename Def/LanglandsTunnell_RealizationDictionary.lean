import Mathlib
import Def.AutomorphicForm_HeckeEigensystem
import Def.FormalHecke_Eigensystem
import Def.LanglandsTunnell_ExplicitLift
import Def.ModularForm_EisensteinChiNegThree
import Def.CuspForm_IntegralLattice

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open FLT.ExplicitLift EisensteinWeightOne CuspForm Zsqrtd

noncomputable section

namespace AutomorphicForm

def ratPrime (p : Nat.Primes) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p

def RealizationDictionary (notion : CuspidalityNotion (ℤ√(-2))) : Prop :=
  ∀ π₀ : HeckeEigensystem ℚ (ℤ√(-2)), notion.IsCusp ℚ π₀ →
    ∀ T : Finset ℕ,
      ∃ (M : ℕ) (_ : NeZero M) (b : ℕ → ℤ√(-2)),
        (∀ ℓ ∈ T, ℓ ≠ 0 → ℓ ∣ M) ∧
        FormalHecke.IsEigensystem
          (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b ∧
        HasIntegralBasis M ∧
        (∃ a : ℕ → ℤ,
          FormalHecke.IsEigensystem
            (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a ∧
          IsLatticeRealized M a ∧
          ∀ n : ℕ, ((a n : ℤ) : ZMod 3) = red (b n)) ∧
        (∃ a : ℕ → ℤ,
          FormalHecke.IsEigensystem
            (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a ∧
          IsLatticeRealized M a ∧
          ∀ n : ℕ, ((a n : ℤ) : ZMod 3) = ((chiNegThree n : ℤ) : ZMod 3) * red (b n)) ∧
        (∀ p : Nat.Primes, ¬ (p : ℕ) ∣ 3 * M → b (p : ℕ) = π₀.a (ratPrime p))

end AutomorphicForm

end
