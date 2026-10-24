import Mathlib
import Lemma.Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option autoImplicit false

noncomputable section

open scoped TensorProduct MatrixGroups
open LT.LatticeTree TensorProduct

namespace CerednikDrinfeld
namespace FormalOmega

section DetIndex

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]

def HasDetIndex (π : 𝒪) (N : Submodule 𝒪 (Fin 2 → K)) (e : ℤ) : Prop :=
  ∃ g : GL (Fin 2) K, latticeMap g (stdLattice 𝒪 K) = N ∧
    ∃ u : 𝒪ˣ, ((Matrix.GeneralLinearGroup.det g : Kˣ) : K) = algebraMap 𝒪 K u * algebraMap 𝒪 K π ^ e

end DetIndex

section Datum

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (B : Type) [CommRing B] [Algebra 𝒪 B]

abbrev locRing (x : PrimeSpectrum B) : Type := Localization.AtPrime x.asIdeal

abbrev toLocRing (x : PrimeSpectrum B) : B →ₐ[𝒪] locRing B x :=
  IsScalarTower.toAlgHom 𝒪 B (locRing B x)

abbrev stalk (x : PrimeSpectrum B) (T : Type) [AddCommGroup T] [Module B T] : Type :=
  LocalizedModule x.asIdeal.primeCompl T

variable {B}

def smulInto {N N' : Submodule 𝒪 (Fin 2 → K)} (h : ∀ v ∈ N, algebraMap 𝒪 K π • v ∈ N') : ↥N →ₗ[𝒪] ↥N' :=
  (DistribSMul.toLinearMap 𝒪 (Fin 2 → K) (algebraMap 𝒪 K π)).restrict h

theorem coe_smulInto_apply {N N' : Submodule 𝒪 (Fin 2 → K)} (h : ∀ v ∈ N, algebraMap 𝒪 K π • v ∈ N') (v : ↥N) :
    ((smulInto π h v : ↥N') : Fin 2 → K) = algebraMap 𝒪 K π • (v : Fin 2 → K) := rfl

variable (B) in

structure DrinfeldDatum : Type 1 where

  N₀ : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K)

  N₁ : PrimeSpectrum B → Submodule 𝒪 (Fin 2 → K)
  full₀ : ∀ x, IsFullLattice (N₀ x)
  full₁ : ∀ x, IsFullLattice (N₁ x)

  le : ∀ x, N₀ x ≤ N₁ x

  smul_le : ∀ x, ∀ v ∈ N₁ x, algebraMap 𝒪 K π • v ∈ N₀ x

  isOpen_setOf_mem₀ : ∀ v : Fin 2 → K, IsOpen {x : PrimeSpectrum B | v ∈ N₀ x}
  isOpen_setOf_mem₁ : ∀ v : Fin 2 → K, IsOpen {x : PrimeSpectrum B | v ∈ N₁ x}

  T₀ : Type
  T₁ : Type
  [addCommGroup₀ : AddCommGroup T₀]
  [module₀ : Module B T₀]
  [addCommGroup₁ : AddCommGroup T₁]
  [module₁ : Module B T₁]
  invertible₀ : Module.Invertible B T₀
  invertible₁ : Module.Invertible B T₁

  Pi₀ : T₀ →ₗ[B] T₁
  Pi₁ : T₁ →ₗ[B] T₀
  Pi₁_Pi₀ : ∀ t, Pi₁ (Pi₀ t) = algebraMap 𝒪 B π • t
  Pi₀_Pi₁ : ∀ t, Pi₀ (Pi₁ t) = algebraMap 𝒪 B π • t

  u₀ : ∀ x : PrimeSpectrum B,
    latticeBaseChange 𝒪 K (locRing B x) ⟨N₀ x, full₀ x⟩ →ₗ[locRing B x] stalk B x T₀

  u₁ : ∀ x : PrimeSpectrum B,
    latticeBaseChange 𝒪 K (locRing B x) ⟨N₁ x, full₁ x⟩ →ₗ[locRing B x] stalk B x T₁

  u₁_incl : ∀ x w, u₁ x (inclBaseChange (locRing B x) (M' := ⟨N₀ x, full₀ x⟩) (M := ⟨N₁ x, full₁ x⟩) (le x) w) =
    LocalizedModule.map x.asIdeal.primeCompl Pi₀ (u₀ x w)

  u₀_smul : ∀ x w, u₀ x (((smulInto π (smul_le x)).baseChange (locRing B x) :
      latticeBaseChange 𝒪 K (locRing B x) ⟨N₁ x, full₁ x⟩ →ₗ[locRing B x] latticeBaseChange 𝒪 K (locRing B x) ⟨N₀ x, full₀ x⟩) w) =
    LocalizedModule.map x.asIdeal.primeCompl Pi₁ (u₁ x w)

  u₀_surjective : ∀ x, Function.Surjective (u₀ x)
  u₁_surjective : ∀ x, Function.Surjective (u₁ x)

  u₀_continuous : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K), v ∈ N₀ x →
    ∃ (f : B) (t : T₀), f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal),
      ∃ hv : v ∈ N₀ y, u₀ y ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(N₀ y))) = LocalizedModule.mk t ⟨f, hy⟩
  u₁_continuous : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K), v ∈ N₁ x →
    ∃ (f : B) (t : T₁), f ∉ x.asIdeal ∧ ∀ (y : PrimeSpectrum B) (hy : f ∉ y.asIdeal),
      ∃ hv : v ∈ N₁ y, u₁ y ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(N₁ y))) = LocalizedModule.mk t ⟨f, hy⟩

  locallyConstant₀ : ∀ x : PrimeSpectrum B, LinearMap.range Pi₀ ≤ x.asIdeal • (⊤ : Submodule B T₁) →
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, LinearMap.range Pi₀ ≤ y.asIdeal • (⊤ : Submodule B T₁) → N₀ y = N₀ x

  locallyConstant₁ : ∀ x : PrimeSpectrum B, LinearMap.range Pi₁ ≤ x.asIdeal • (⊤ : Submodule B T₀) →
    ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, LinearMap.range Pi₁ ≤ y.asIdeal • (⊤ : Submodule B T₀) → N₁ y = N₁ x

  injective₀ : ∀ (x : PrimeSpectrum B) (v : ↥(N₀ x)),
    u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl Pi₁)).restrictScalars B ⊔
        x.asIdeal • (⊤ : Submodule B (stalk B x T₀)) →
    ∃ w ∈ N₁ x, (v : Fin 2 → K) = algebraMap 𝒪 K π • w

  injective₁ : ∀ (x : PrimeSpectrum B) (v : ↥(N₁ x)),
    u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] v) ∈
      (LinearMap.range (LocalizedModule.map x.asIdeal.primeCompl Pi₀)).restrictScalars B ⊔
        x.asIdeal • (⊤ : Submodule B (stalk B x T₁)) →
    (v : Fin 2 → K) ∈ N₀ x

  hasDetIndex₀ : ∀ x : PrimeSpectrum B, LinearMap.range Pi₀ ≤ x.asIdeal • (⊤ : Submodule B T₁) → HasDetIndex π (N₀ x) 0

  hasDetIndex₁ : ∀ x : PrimeSpectrum B, LinearMap.range Pi₁ ≤ x.asIdeal • (⊤ : Submodule B T₀) → HasDetIndex π (N₁ x) (-1)

attribute [instance] DrinfeldDatum.addCommGroup₀ DrinfeldDatum.module₀ DrinfeldDatum.addCommGroup₁ DrinfeldDatum.module₁
  DrinfeldDatum.invertible₀ DrinfeldDatum.invertible₁

namespace DrinfeldDatum

variable {π}

abbrev L₀ (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) : FullLattice 𝒪 K := ⟨Q.N₀ x, Q.full₀ x⟩

abbrev L₁ (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) : FullLattice 𝒪 K := ⟨Q.N₁ x, Q.full₁ x⟩

def stratum₀ (Q : DrinfeldDatum (K := K) π B) : Set (PrimeSpectrum B) :=
  {x | LinearMap.range Q.Pi₀ ≤ x.asIdeal • (⊤ : Submodule B Q.T₁)}

def stratum₁ (Q : DrinfeldDatum (K := K) π B) : Set (PrimeSpectrum B) :=
  {x | LinearMap.range Q.Pi₁ ≤ x.asIdeal • (⊤ : Submodule B Q.T₀)}

structure Iso (Q Q' : DrinfeldDatum (K := K) π B) : Type where
  N₀_eq : ∀ x, Q.N₀ x = Q'.N₀ x
  N₁_eq : ∀ x, Q.N₁ x = Q'.N₁ x
  τ₀ : Q.T₀ ≃ₗ[B] Q'.T₀
  τ₁ : Q.T₁ ≃ₗ[B] Q'.T₁
  τ₁_Pi₀ : ∀ t, τ₁ (Q.Pi₀ t) = Q'.Pi₀ (τ₀ t)
  τ₀_Pi₁ : ∀ t, τ₀ (Q.Pi₁ t) = Q'.Pi₁ (τ₁ t)
  τ₀_u₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K) (hv : v ∈ Q.N₀ x) (hv' : v ∈ Q'.N₀ x),
    Q'.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Q'.N₀ x))) =
      LocalizedModule.map x.asIdeal.primeCompl τ₀.toLinearMap (Q.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q.N₀ x))))
  τ₁_u₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K) (hv : v ∈ Q.N₁ x) (hv' : v ∈ Q'.N₁ x),
    Q'.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Q'.N₁ x))) =
      LocalizedModule.map x.asIdeal.primeCompl τ₁.toLinearMap (Q.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q.N₁ x))))

def IsIsomorphic (Q Q' : DrinfeldDatum (K := K) π B) : Prop := Nonempty (Iso Q Q')

def IsQuadrupleOf (Q : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B) : Prop :=
  ∀ x : PrimeSpectrum B,
    d.EdgeNondegAt π x.asIdeal (Q.L₀ x) (Q.L₁ x) ∧
    LinearMap.ker (Q.u₀ x) = (d.map π (toLocRing B x)).line (Q.L₀ x) ∧
    LinearMap.ker (Q.u₁ x) = (d.map π (toLocRing B x)).line (Q.L₁ x)

theorem IsQuadrupleOf.edge_iff (Q : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B) (x : PrimeSpectrum B) :
    d.EdgeNondegAt π x.asIdeal (Q.L₀ x) (Q.L₁ x) ↔
    (Q.N₀ x ≤ Q.N₁ x ∧ (∀ v : ↥(Q.N₁ x), algebraMap 𝒪 K π • (v : Fin 2 → K) ∈ Q.N₀ x) ∧
      (∀ v : ↥(Q.N₁ x), (v : Fin 2 → K) ∉ Q.N₀ x →
        (1 : B) ⊗ₜ[𝒪] v ∉ d.line (Q.L₁ x) ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Q.L₁ x)))) ∧
      (∀ v' : ↥(Q.N₀ x), (¬ ∃ w : ↥(Q.N₁ x), (v' : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K)) →
        (1 : B) ⊗ₜ[𝒪] v' ∉ d.line (Q.L₀ x) ⊔ (x.asIdeal • ⊤ : Submodule B (latticeBaseChange 𝒪 K B (Q.L₀ x))))) :=
  Iff.rfl

end DrinfeldDatum

end Datum

end FormalOmega
end CerednikDrinfeld

end
