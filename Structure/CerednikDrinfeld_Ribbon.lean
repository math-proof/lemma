import Def.ModularCurve_ComponentGroup
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.PNat.Defs
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Quotient.Defs

set_option autoImplicit false

namespace CerednikDrinfeld

open ModularCurve

variable {E V : Type*}

structure DegeneracyData (E V : Type*) where
  a : E → V
  b : E → V
  w : E → ℕ+

def degeneracyMatrix [DecidableEq V] (f : E → V) : Matrix V E ℤ :=
  Matrix.of fun v e => if f e = v then 1 else 0

def pushforward [Fintype E] [DecidableEq V] (f : E → V) : (E → ℤ) →ₗ[ℤ] (V → ℤ) :=
  (degeneracyMatrix f).mulVecLin

def jointDelta [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    Fin 2 → ((E → ℤ) →ₗ[ℤ] (V → ℤ)) :=
  ![pushforward D.a, pushforward D.b]

def ribbonKernel [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    Submodule ℤ (E → ℤ) :=
  ⨅ i, LinearMap.ker (jointDelta D i)


structure HeckeData [Fintype E] [Fintype V] [DecidableEq V] (D : DegeneracyData E V) where
  T : Nat.Primes → Matrix E E ℤ
  Tv : Nat.Primes → Matrix V V ℤ
  comm : ∀ ℓ ℓ' : Nat.Primes, Commute (T ℓ) (T ℓ')
  commv : ∀ ℓ ℓ' : Nat.Primes, Commute (Tv ℓ) (Tv ℓ')
  S : Finset Nat.Primes
  good_equivariant : ∀ ℓ : Nat.Primes, ℓ ∉ S → ∀ i : Fin 2, ∀ x : E → ℤ,
    jointDelta D i ((T ℓ).mulVecLin x) = (Tv ℓ).mulVecLin (jointDelta D i x)
  kernel_stable : ∀ ℓ : Nat.Primes, ∀ x : E → ℤ, (∀ i, jointDelta D i x = 0) →
    ∀ i, jointDelta D i ((T ℓ).mulVecLin x) = 0


variable {E₁ V₁ E₂ V₂ : Type*}

structure Matching [Fintype E₁] [Fintype V₁] [DecidableEq V₁]
    [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {D₂ : DegeneracyData E₂ V₂}
    (H₁ : HeckeData D₁) (H₂ : HeckeData D₂) where
  eE : E₁ ≃ E₂
  eV : V₁ ≃ V₂
  map_a : ∀ e, D₂.a (eE e) = eV (D₁.a e)
  map_b : ∀ e, D₂.b (eE e) = eV (D₁.b e)
  map_w : ∀ e, D₂.w (eE e) = D₁.w e
  bad : Finset Nat.Primes
  away_intertwine : ∀ ℓ : Nat.Primes, ℓ ∉ bad → ∀ x : E₁ → ℤ,
    (H₂.T ℓ).mulVecLin (x ∘ eE.symm) = ((H₁.T ℓ).mulVecLin x) ∘ eE.symm
  bad_kernel_intertwine : ∀ ℓ : Nat.Primes, ℓ ∈ bad → ∀ x ∈ ribbonKernel D₁,
    (H₂.T ℓ).mulVecLin (x ∘ eE.symm) = ((H₁.T ℓ).mulVecLin x) ∘ eE.symm

end CerednikDrinfeld
