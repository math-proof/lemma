import Mathlib
import Lemma.Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option autoImplicit false

noncomputable section

open scoped TensorProduct MatrixGroups
open LT.LatticeTree TensorProduct Matrix

namespace CerednikDrinfeld
namespace FormalOmega
namespace DrinfeldDatum

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

section BaseChange

variable {B' : Type} [CommRing B'] [Algebra 𝒪 B']

abbrev pointUnder (f : B →ₐ[𝒪] B') (x' : PrimeSpectrum B') : PrimeSpectrum B :=
  PrimeSpectrum.comap (f : B →+* B') x'

structure BaseChangeAlong (f : B →ₐ[𝒪] B') (Q : DrinfeldDatum (K := K) π B) (Q' : DrinfeldDatum (K := K) π B') :
    Type where

  N₀_eq : ∀ x' : PrimeSpectrum B', Q'.N₀ x' = Q.N₀ (pointUnder f x')

  N₁_eq : ∀ x' : PrimeSpectrum B', Q'.N₁ x' = Q.N₁ (pointUnder f x')

  τ₀ : Q.T₀ →ₛₗ[(f : B →+* B')] Q'.T₀

  τ₁ : Q.T₁ →ₛₗ[(f : B →+* B')] Q'.T₁

  span_range_τ₀ : Submodule.span B' (Set.range τ₀) = ⊤

  span_range_τ₁ : Submodule.span B' (Set.range τ₁) = ⊤

  τ₁_Pi₀ : ∀ t, τ₁ (Q.Pi₀ t) = Q'.Pi₀ (τ₀ t)

  τ₀_Pi₁ : ∀ t, τ₀ (Q.Pi₁ t) = Q'.Pi₁ (τ₁ t)

  u₀_eq : ∀ (x' : PrimeSpectrum B') (v : Fin 2 → K) (hv : v ∈ Q.N₀ (pointUnder f x')) (hv' : v ∈ Q'.N₀ x')
    (t : Q.T₀) (s : B) (hs : f s ∉ x'.asIdeal),
    Q.u₀ (pointUnder f x') ((1 : locRing B (pointUnder f x')) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q.N₀ (pointUnder f x')))) =
      LocalizedModule.mk t (⟨s, hs⟩ : (pointUnder f x').asIdeal.primeCompl) →
    Q'.u₀ x' ((1 : locRing B' x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Q'.N₀ x'))) =
      LocalizedModule.mk (τ₀ t) (⟨f s, hs⟩ : x'.asIdeal.primeCompl)

  u₁_eq : ∀ (x' : PrimeSpectrum B') (v : Fin 2 → K) (hv : v ∈ Q.N₁ (pointUnder f x')) (hv' : v ∈ Q'.N₁ x')
    (t : Q.T₁) (s : B) (hs : f s ∉ x'.asIdeal),
    Q.u₁ (pointUnder f x') ((1 : locRing B (pointUnder f x')) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q.N₁ (pointUnder f x')))) =
      LocalizedModule.mk t (⟨s, hs⟩ : (pointUnder f x').asIdeal.primeCompl) →
    Q'.u₁ x' ((1 : locRing B' x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Q'.N₁ x'))) =
      LocalizedModule.mk (τ₁ t) (⟨f s, hs⟩ : x'.asIdeal.primeCompl)

def IsBaseChangeAlong (f : B →ₐ[𝒪] B') (Q : DrinfeldDatum (K := K) π B) (Q' : DrinfeldDatum (K := K) π B') : Prop :=
  Nonempty (BaseChangeAlong f Q Q')

end BaseChange

section Translate

structure TranslateEven (g : GL (Fin 2) K) (c : Kˣ) (Q Q' : DrinfeldDatum (K := K) π B) : Type where

  N₀_eq : ∀ x : PrimeSpectrum B, Q'.N₀ x = latticeMap (scalarGL c * g⁻¹) (Q.N₀ x)

  N₁_eq : ∀ x : PrimeSpectrum B, Q'.N₁ x = latticeMap (scalarGL c * g⁻¹) (Q.N₁ x)

  τ₀ : Q.T₀ ≃ₗ[B] Q'.T₀

  τ₁ : Q.T₁ ≃ₗ[B] Q'.T₁
  τ₁_Pi₀ : ∀ t, τ₁ (Q.Pi₀ t) = Q'.Pi₀ (τ₀ t)
  τ₀_Pi₁ : ∀ t, τ₀ (Q.Pi₁ t) = Q'.Pi₁ (τ₁ t)

  τ₀_u₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K) (hv : v ∈ Q.N₀ x)
    (hv' : ((scalarGL c * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ Q'.N₀ x),
    Q'.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hv'⟩ : ↥(Q'.N₀ x))) =
      LocalizedModule.map x.asIdeal.primeCompl τ₀.toLinearMap (Q.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q.N₀ x))))

  τ₁_u₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K) (hv : v ∈ Q.N₁ x)
    (hv' : ((scalarGL c * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ Q'.N₁ x),
    Q'.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hv'⟩ : ↥(Q'.N₁ x))) =
      LocalizedModule.map x.asIdeal.primeCompl τ₁.toLinearMap (Q.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q.N₁ x))))

def IsTranslateEven (g : GL (Fin 2) K) (c : Kˣ) (Q Q' : DrinfeldDatum (K := K) π B) : Prop :=
  Nonempty (TranslateEven g c Q Q')

structure TranslateOdd (g : GL (Fin 2) K) (c₀ c₁ : Kˣ) (Q Q' : DrinfeldDatum (K := K) π B) : Type where

  c₀_eq : (c₀ : K) = algebraMap 𝒪 K π * c₁

  N₀_eq : ∀ x : PrimeSpectrum B, Q'.N₀ x = latticeMap (scalarGL c₀ * g⁻¹) (Q.N₁ x)

  N₁_eq : ∀ x : PrimeSpectrum B, Q'.N₁ x = latticeMap (scalarGL c₁ * g⁻¹) (Q.N₀ x)

  σ₀ : Q.T₁ ≃ₗ[B] Q'.T₀

  σ₁ : Q.T₀ ≃ₗ[B] Q'.T₁
  σ₁_Pi₁ : ∀ t, σ₁ (Q.Pi₁ t) = Q'.Pi₀ (σ₀ t)
  σ₀_Pi₀ : ∀ t, σ₀ (Q.Pi₀ t) = Q'.Pi₁ (σ₁ t)

  σ₀_u₀ : ∀ (x : PrimeSpectrum B) (w : Fin 2 → K) (hw : w ∈ Q.N₁ x)
    (hw' : ((scalarGL c₀ * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w ∈ Q'.N₀ x),
    Q'.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hw'⟩ : ↥(Q'.N₀ x))) =
      LocalizedModule.map x.asIdeal.primeCompl σ₀.toLinearMap (Q.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨w, hw⟩ : ↥(Q.N₁ x))))

  σ₁_u₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K) (hv : v ∈ Q.N₀ x)
    (hv' : ((scalarGL c₁ * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ Q'.N₁ x),
    Q'.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hv'⟩ : ↥(Q'.N₁ x))) =
      LocalizedModule.map x.asIdeal.primeCompl σ₁.toLinearMap (Q.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q.N₀ x))))

def IsTranslateOdd (g : GL (Fin 2) K) (c₀ c₁ : Kˣ) (Q Q' : DrinfeldDatum (K := K) π B) : Prop :=
  Nonempty (TranslateOdd g c₀ c₁ Q Q')

def Iso.toTranslateEven {Q Q' : DrinfeldDatum (K := K) π B} (e : Iso Q Q') : TranslateEven 1 1 Q Q' where
  N₀_eq x := by rw [scalarGL_one, one_mul, inv_one, latticeMap_one]; exact (e.N₀_eq x).symm
  N₁_eq x := by rw [scalarGL_one, one_mul, inv_one, latticeMap_one]; exact (e.N₁_eq x).symm
  τ₀ := e.τ₀
  τ₁ := e.τ₁
  τ₁_Pi₀ := e.τ₁_Pi₀
  τ₀_Pi₁ := e.τ₀_Pi₁
  τ₀_u₀ x v hv hv' := by
    have h1 : ((scalarGL (1 : Kˣ) * (1 : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v := by
      rw [scalarGL_one, one_mul, inv_one, Units.val_one, Matrix.one_mulVec]
    have hv'' : v ∈ Q'.N₀ x := by rw [← h1]; exact hv'
    have key := e.τ₀_u₀ x v hv hv''
    have hsub : (⟨_, hv'⟩ : ↥(Q'.N₀ x)) = ⟨v, hv''⟩ := Subtype.ext h1
    rw [hsub]; exact key
  τ₁_u₁ x v hv hv' := by
    have h1 : ((scalarGL (1 : Kˣ) * (1 : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v := by
      rw [scalarGL_one, one_mul, inv_one, Units.val_one, Matrix.one_mulVec]
    have hv'' : v ∈ Q'.N₁ x := by rw [← h1]; exact hv'
    have key := e.τ₁_u₁ x v hv hv''
    have hsub : (⟨_, hv'⟩ : ↥(Q'.N₁ x)) = ⟨v, hv''⟩ := Subtype.ext h1
    rw [hsub]; exact key

end Translate

end DrinfeldDatum
end FormalOmega
end CerednikDrinfeld

end
