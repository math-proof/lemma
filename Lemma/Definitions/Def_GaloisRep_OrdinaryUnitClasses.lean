import Mathlib
import Lemma.Definitions.Def_GaloisRep_AdZero
import Lemma.Definitions.Def_GroupCohomology_TangentSpace
import Lemma.Definitions.Def_ExtEndgame_ProductionDatum
import Lemma.Definitions.Def_GaloisRep_LocalFlatClasses
import Lemma.Definitions.Def_GaloisRep_CompletionBridge
import Lemma.Definitions.Def_FLTPrelim_Ramification

set_option autoImplicit false

open CategoryTheory groupCohomology ExtCitation

namespace ResidualGaloisRep

variable {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)

def unitRootInertia : Set (primeLocalGaloisGroup (pPrime p)) :=
  {σ | localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ∧
    (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → localAut p σ ζ = ζ) ∧
    ∀ β : PadicAlgCl p, ‖β‖₊ = 1 →
      (∀ τ : primeLocalGaloisGroup (pPrime p),
        localAut p τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → localAut p τ (β ^ p) = β ^ p) →
      localAut p σ β = β}

def IsOrdinaryCocycleAd (V₁ : Submodule k ρbar.V)
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))) : Prop :=
  (∀ (σ : primeLocalGaloisGroup (pPrime p)), ∀ v ∈ V₁,
    c.val σ v ∈ V₁) ∧
  (∀ (σ : primeLocalGaloisGroup (pPrime p)),
    localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
      (∀ v : ρbar.V, c.val σ v ∈ V₁) ∧
      ∀ v ∈ V₁, c.val σ v = 0)

def IsOrdinaryUnitCocycleAd (V₁ : Submodule k ρbar.V)
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))) : Prop :=
  ρbar.IsOrdinaryCocycleAd p V₁ c ∧
  (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ (g s : primeLocalGaloisGroup (pPrime p)),
      primeLocalToGlobal (pPrime p) s ∈ F.fixingSubgroup → c.val (g * s) = c.val g) ∧
  ∀ σ ∈ unitRootInertia p, c.val σ = 0

noncomputable def ordinaryUnitClassesAd (V₁ : Submodule k ρbar.V) :
    Submodule k (H1 (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))) :=
  Submodule.span k
    {y | ∃ c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)),
      ρbar.IsOrdinaryUnitCocycleAd p V₁ c ∧
        y = (H1π (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))).hom c}

end ResidualGaloisRep
