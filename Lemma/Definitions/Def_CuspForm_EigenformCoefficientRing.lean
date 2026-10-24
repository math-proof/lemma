import Mathlib
import Lemma.Definitions.Def_FLTPrelim_Modularity

set_option autoImplicit false

noncomputable section

namespace CuspForm

open scoped CongruenceSubgroup

variable {M : ℕ} (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)

def PrimeCoeffsIntegral : Prop :=
  ∀ ℓ : Nat.Primes, ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ

variable {g} (hint : PrimeCoeffsIntegral g)

def eigenLift (ℓ : Nat.Primes) : integralClosure ℤ ℂ := (hint ℓ).choose

theorem eigenLift_coe (ℓ : Nat.Primes) : ((eigenLift hint ℓ : integralClosure ℤ ℂ) : ℂ) = ModularFormClass.qCoeff g ℓ :=
  (hint ℓ).choose_spec

def eigenCoeffRing : Subalgebra ℤ (integralClosure ℤ ℂ) :=
  Algebra.adjoin ℤ (Set.range (eigenLift hint))

theorem eigenLift_mem_eigenCoeffRing (ℓ : Nat.Primes) : eigenLift hint ℓ ∈ eigenCoeffRing hint :=
  Algebra.subset_adjoin ⟨ℓ, rfl⟩

variable (𝔪w : Ideal (integralClosure ℤ ℂ))

def eigenResidueIdeal : Ideal (eigenCoeffRing hint) :=
  Ideal.comap (algebraMap (eigenCoeffRing hint) (integralClosure ℤ ℂ)) 𝔪w

abbrev EigenResidueRing : Type := eigenCoeffRing hint ⧸ eigenResidueIdeal hint 𝔪w

def eigenSystemMod : Nat.Primes → EigenResidueRing hint 𝔪w :=
  fun ℓ => Ideal.Quotient.mk _ ⟨eigenLift hint ℓ, eigenLift_mem_eigenCoeffRing hint ℓ⟩

end CuspForm

end
