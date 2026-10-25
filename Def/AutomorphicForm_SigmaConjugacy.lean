import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

variable {L : Type*} [Field L]

def sigmaConj (σ : L →+* L) (g δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    Matrix.GeneralLinearGroup (Fin 2) L :=
  g * δ * (Matrix.GeneralLinearGroup.map σ g)⁻¹

def IsSigmaConj (σ : L →+* L) (δ δ' : Matrix.GeneralLinearGroup (Fin 2) L) : Prop :=
  ∃ g, δ' = sigmaConj σ g δ

def sigmaConjClassOf (σ : L →+* L) (δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    Set (Matrix.GeneralLinearGroup (Fin 2) L) :=
  {δ' | IsSigmaConj σ δ δ'}

end AutomorphicForm

end
