import Mathlib
import Lemma.ModularCurve.ToricDescentData
import Def.ModularCurve_ToricDichotomyData

set_option autoImplicit false

noncomputable section

namespace ModularCurve


section Bundle


namespace ExistsToricDichotomyDataQGuarded

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
  {q : Nat.Primes} {S : Finset Nat.Primes} {I : Subgroup G} {φ : G}
  {J₀ : Type*} [AddCommGroup J₀] [Module HeckeAlg J₀]


theorem toricFrobeniusSq (h : ExistsToricDichotomyDataQGuarded J q S I φ J₀) :
    ToricFrobeniusSq (q : ℕ) φ h.toric :=
  h.choose_spec.1

theorem toricDichotomy (h : ExistsToricDichotomyDataQGuarded J q S I φ J₀) :
    IsToricDichotomyQGuarded (q : ℕ) S I h.toric J₀ :=
  h.choose_spec.2.1

theorem toricFrobeniusHecke (h : ExistsToricDichotomyDataQGuarded J q S I φ J₀) :
    ToricFrobeniusHecke q φ h.toric :=
  h.choose_spec.2.2

end ExistsToricDichotomyDataQGuarded

end Bundle

end ModularCurve

end
