import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Def.AutomorphicForm_GL2ConjugacyCells

set_option autoImplicit false

open Matrix Polynomial

noncomputable section

namespace AutomorphicForm

variable {K : Type*} [Field K]


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

end
