import Lemma.Definitions.Def_FLTPrelim_Modularity

set_option autoImplicit false

namespace ModPForms

def modPCusp (N : ℕ) (k : ℤ) (F : Type) [Field F] : Submodule F (PowerSeries F) :=
  Submodule.span F
    {φ | ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (a : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧ φ = PowerSeries.mk fun n => ((a n : ℤ) : F)}

def modPMod (N : ℕ) (k : ℤ) (F : Type) [Field F] : Submodule F (PowerSeries F) :=
  Submodule.span F
    {φ | ∃ (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (a : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧ φ = PowerSeries.mk fun n => ((a n : ℤ) : F)}

noncomputable def thetaPS {F : Type} [Field F] (φ : PowerSeries F) : PowerSeries F :=
  PowerSeries.mk fun n => (n : F) * PowerSeries.coeff n φ

noncomputable def heckePS {F : Type} [Field F] (k : ℤ) (ℓ : ℕ) (φ : PowerSeries F) : PowerSeries F :=
  PowerSeries.mk fun n =>
    PowerSeries.coeff (n * ℓ) φ + if ℓ ∣ n then (ℓ : F) ^ (k - 1) * PowerSeries.coeff (n / ℓ) φ else 0

def IsModPEigen {F : Type} [Field F] (N : ℕ) (S₀ : Set ℕ) (k : ℤ) (φ : PowerSeries F) (lam : ℕ → F) : Prop :=
  φ ≠ 0 ∧
    ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → heckePS k ℓ φ = lam ℓ • φ

end ModPForms
