import Mathlib
import Def.LanglandsTunnell_RealizationDictionary
import Def.LanglandsTunnell_TunnellExistenceCarriers

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open FLT.ExplicitLift EisensteinWeightOne CuspForm Zsqrtd
open CongruenceSubgroup

noncomputable section

namespace CuspForm

def IsWeightOneChiNegThreeRealized (M : ℕ) (b : ℕ → ℤ√(-2)) : Prop :=
  ∃ (ι : ℤ√(-2) →+* ℂ) (f : CuspForm (Gamma1 M) 1),
    ∀ n : ℕ, ModularFormClass.qCoeff f n = ι (b n)

end CuspForm

namespace AutomorphicForm

def WeightOneHolomorphicRealization (notion : CuspidalityNotion (ℤ√(-2))) : Prop :=
  ∀ π₀ : HeckeEigensystem ℚ (ℤ√(-2)), notion.IsCusp ℚ π₀ →
    ∀ T : Finset ℕ,
      ∃ (M : ℕ) (_ : NeZero M) (b : ℕ → ℤ√(-2)),
        (∀ ℓ ∈ T, ℓ ≠ 0 → ℓ ∣ M) ∧
        FormalHecke.IsEigensystem
          (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b ∧
        HasIntegralBasis M ∧
        CuspForm.IsWeightOneChiNegThreeRealized M b ∧
        (∀ p : Nat.Primes, ¬ (p : ℕ) ∣ 3 * M → b (p : ℕ) = π₀.a (ratPrime p))

end AutomorphicForm

namespace CuspForm

def WeightTwoModThreeCongruenceLift : Prop :=
  ∀ (M : ℕ) (_ : NeZero M) (b : ℕ → ℤ√(-2)),
    FormalHecke.IsEigensystem
      (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b →
    HasIntegralBasis M →
    IsWeightOneChiNegThreeRealized M b →
    (∃ a : ℕ → ℤ,
      FormalHecke.IsEigensystem
        (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a ∧
      IsLatticeRealized M a ∧
      ∀ n : ℕ, ((a n : ℤ) : ZMod 3) = red (b n)) ∧
    (∃ a : ℕ → ℤ,
      FormalHecke.IsEigensystem
        (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a ∧
      IsLatticeRealized M a ∧
      ∀ n : ℕ, ((a n : ℤ) : ZMod 3) = ((chiNegThree n : ℤ) : ZMod 3) * red (b n))

end CuspForm

end
