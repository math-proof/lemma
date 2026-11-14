import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Def.AutomorphicForm_SigmaConjugacy

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

variable {L : Type*} [Field L]


theorem sigmaConj_one_left (σ : L →+* L) (δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    sigmaConj σ 1 δ = δ := by
  simp [sigmaConj]

theorem IsSigmaConj.refl (σ : L →+* L) (δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    IsSigmaConj σ δ δ :=
  ⟨1, (sigmaConj_one_left σ δ).symm⟩

theorem mem_sigmaConjClassOf_self (σ : L →+* L)
    (δ : Matrix.GeneralLinearGroup (Fin 2) L) : δ ∈ sigmaConjClassOf σ δ :=
  IsSigmaConj.refl σ δ

theorem mem_sigmaConjClassOf_iff (σ : L →+* L)
    (δ δ' : Matrix.GeneralLinearGroup (Fin 2) L) :
    δ' ∈ sigmaConjClassOf σ δ ↔ ∃ g, δ' = sigmaConj σ g δ :=
  Iff.rfl

theorem sigmaConj_id (g δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    sigmaConj (RingHom.id L) g δ = g * δ * g⁻¹ := by
  have hmap : Matrix.GeneralLinearGroup.map (RingHom.id L) g = g := by
    ext i j
    simp [Matrix.GeneralLinearGroup.map]
  rw [sigmaConj, hmap]

end AutomorphicForm

end
