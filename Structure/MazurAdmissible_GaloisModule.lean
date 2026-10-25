import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Compat_Mathlib430

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace MazurAdmissible

universe u

local notation "Qbar" => AlgebraicClosure ℚ

structure OpenAction (M : Type u) [AddCommGroup M] where

  φ : (Qbar ≃ₐ[ℚ] Qbar) →* AddAut M

  hker : IsOpen (φ.ker : Set (Qbar ≃ₐ[ℚ] Qbar))

variable {M : Type u} [AddCommGroup M]

def IsTrivialStep (Φ : OpenAction M) (A B : AddSubgroup M) : Prop :=
  ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ x ∈ B, Φ.φ σ x - x ∈ A

def IsCyclotomicStep (p : ℕ) (Φ : OpenAction M) (A B : AddSubgroup M) : Prop :=
  ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ ζ : Qbar, IsPrimitiveRoot ζ p → ∀ a : ℕ, σ ζ = ζ ^ a →
    ∀ x ∈ B, Φ.φ σ x - a • x ∈ A

structure AdmissibleChain (p : ℕ) (Φ : OpenAction M) where

  n : ℕ

  step : Fin (n + 1) → AddSubgroup M

  hbot : step 0 = ⊥

  htop : step (Fin.last n) = ⊤

  hmono : ∀ i : Fin n, step i.castSucc ≤ step i.succ

  tag : Fin n → Bool

  hcard : ∀ i : Fin n,
    Nat.card (↥(step i.succ) ⧸ (step i.castSucc).addSubgroupOf (step i.succ)) = p

  hact : ∀ i : Fin n,
    if tag i then IsTrivialStep Φ (step i.castSucc) (step i.succ)
      else IsCyclotomicStep p Φ (step i.castSucc) (step i.succ)


end MazurAdmissible
