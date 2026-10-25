import Mathlib
import Instance.FLTPrelim_Modularity
import Def.ModularForm_EisensteinChiNegThree

set_option autoImplicit false

open ModularFormClass CongruenceSubgroup EisensteinWeightOne

namespace CuspForm

def qIntegralSet (N : ℕ) : Set (CuspForm (Gamma0 N) 2) :=
  {f | ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ (⊥ : Subring ℂ)}

def qIntegralLattice (N : ℕ) : Submodule ℤ (CuspForm (Gamma0 N) 2) :=
  Submodule.span ℤ (qIntegralSet N)

def HasIntegralBasis (N : ℕ) : Prop :=
  Submodule.span ℂ (qIntegralSet N) = ⊤

end CuspForm

noncomputable def bridgeProduct {R : Type*} [CommRing R] (a : ℕ → R) : PowerSeries R :=
  PowerSeries.mk a * e1Chi3In R

namespace CuspForm

def IsLatticeRealized (N : ℕ) (a : ℕ → ℤ) : Prop :=
  ∃ f : CuspForm (Gamma0 N) 2, f ∈ qIntegralSet N ∧
    ∃ af : ℕ → ℤ, (∀ n, (af n : ℂ) = ModularFormClass.qCoeff f n) ∧
      ∀ n, (3 : ℤ) ∣ af n - (bridgeProduct a).coeff n

end CuspForm
