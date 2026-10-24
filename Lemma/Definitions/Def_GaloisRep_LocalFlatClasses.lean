import Mathlib
import Lemma.Definitions.Def_GaloisRep_AdZero
import Lemma.Definitions.Def_GroupCohomology_TangentSpace
import Lemma.Definitions.Def_ExtEndgame_ProductionDatum

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

namespace ResidualGaloisRep

variable {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)

def localAut (σ : primeLocalGaloisGroup (pPrime p)) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p := σ

noncomputable def dualLiftModuleAct
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero))
    (σ : primeLocalGaloisGroup (pPrime p)) (x : ρbar.V × ρbar.V) : ρbar.V × ρbar.V :=
  (ρbar.ρ (primeLocalToGlobal (pPrime p) σ) x.1,
    ((c : primeLocalGaloisGroup (pPrime p) → ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ :
        Module.End k ρbar.V) (ρbar.ρ (primeLocalToGlobal (pPrime p) σ) x.1)
      + ρbar.ρ (primeLocalToGlobal (pPrime p) σ) x.2)

def IsLocallyFlatCocycle
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)) : Prop :=
  ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
    Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
    ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
      (∀ f g, e (f * g) = e f + e g) ∧
      ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
        (∀ h : H, g h = localAut p σ (f h)) → e g = ρbar.dualLiftModuleAct p c σ (e f)

noncomputable def localFlatClasses :
    Submodule k (H1 (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)) :=
  Submodule.span k
    {y | ∃ c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero),
      ρbar.IsLocallyFlatCocycle p c ∧
        y = (H1π (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)).hom c}

noncomputable def dualLiftModuleActAd
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)))
    (σ : primeLocalGaloisGroup (pPrime p)) (x : ρbar.V × ρbar.V) : ρbar.V × ρbar.V :=
  (ρbar.ρ (primeLocalToGlobal (pPrime p) σ) x.1,
    ((c : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) σ)
        (ρbar.ρ (primeLocalToGlobal (pPrime p) σ) x.1)
      + ρbar.ρ (primeLocalToGlobal (pPrime p) σ) x.2)

def IsLocallyFlatCocycleAd
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))) : Prop :=
  ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
    Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
    ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
      (∀ f g, e (f * g) = e f + e g) ∧
      ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
        (∀ h : H, g h = localAut p σ (f h)) → e g = ρbar.dualLiftModuleActAd p c σ (e f)

noncomputable def localFlatClassesAd :
    Submodule k (H1 (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))) :=
  Submodule.span k
    {y | ∃ c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)),
      ρbar.IsLocallyFlatCocycleAd p c ∧
        y = (H1π (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))).hom c}

end ResidualGaloisRep
