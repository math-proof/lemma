import Mathlib
import Lemma.Definitions.Def_LanglandsTunnell_RealizationDictionary
import Lemma.Definitions.Def_LanglandsTunnell_TunnellExistenceCarriers

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

namespace AutomorphicForm

theorem realizationDictionary_of_weightOne_of_congruenceLift
    {notion : CuspidalityNotion (ℤ√(-2))}
    (hW1 : WeightOneHolomorphicRealization notion)
    (hW2 : CuspForm.WeightTwoModThreeCongruenceLift) :
    RealizationDictionary notion := by
  intro π₀ hcusp T
  obtain ⟨M, hM, b, c1, c2, c3, cW1, c6⟩ := hW1 π₀ hcusp T
  obtain ⟨c4, c5⟩ := hW2 M hM b c2 c3 cW1
  exact ⟨M, hM, b, c1, c2, c3, c4, c5, c6⟩

end AutomorphicForm

namespace LanglandsTunnell

theorem notionCompatForAttachedOctahedralData_self
    (notion : AutomorphicForm.CuspidalityNotion (ℤ√(-2))) :
    NotionCompatForAttachedOctahedralData notion notion :=
  fun _ _ _ _ _ _ _ _ h _ => h

end LanglandsTunnell

end
