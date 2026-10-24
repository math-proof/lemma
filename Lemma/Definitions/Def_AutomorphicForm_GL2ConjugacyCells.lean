import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option autoImplicit false

open Matrix Polynomial

noncomputable section

namespace AutomorphicForm

variable {K : Type*} [Field K]

def IsCentralType (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∃ c : K, M = c • (1 : Matrix (Fin 2) (Fin 2) K)

def IsUnipotentType (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ¬IsCentralType M ∧ ∃ a : K, M.charpoly = (X - C a) ^ 2

def IsHyperbolicType (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∃ a b : K, a ≠ b ∧ M.charpoly = (X - C a) * (X - C b)

def IsEllipticType (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∀ a : K, ¬M.charpoly.IsRoot a

def centralCell (K : Type*) [Field K] : Set (GL (Fin 2) K) :=
  {γ | IsCentralType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)}

def unipotentCell (K : Type*) [Field K] : Set (GL (Fin 2) K) :=
  {γ | IsUnipotentType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)}

def hyperbolicCell (K : Type*) [Field K] : Set (GL (Fin 2) K) :=
  {γ | IsHyperbolicType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)}

def ellipticCell (K : Type*) [Field K] : Set (GL (Fin 2) K) :=
  {γ | IsEllipticType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)}

theorem mem_centralCell_iff {γ : GL (Fin 2) K} :
    γ ∈ centralCell K ↔ IsCentralType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  Iff.rfl

theorem mem_unipotentCell_iff {γ : GL (Fin 2) K} :
    γ ∈ unipotentCell K ↔ IsUnipotentType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  Iff.rfl

theorem mem_hyperbolicCell_iff {γ : GL (Fin 2) K} :
    γ ∈ hyperbolicCell K ↔ IsHyperbolicType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  Iff.rfl

theorem mem_ellipticCell_iff {γ : GL (Fin 2) K} :
    γ ∈ ellipticCell K ↔ IsEllipticType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  Iff.rfl

end AutomorphicForm
