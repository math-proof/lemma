/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GameTheory/ShapleyValue.lean -/


import Theorem.GameTheory.ShapleyValue.Part3
import Lemma.Set.ShapleyValue


namespace MathlibExt.GameTheory.ShapleyValue

open scoped BigOperators

/-- Former Wanted theorem shape, generic in the player type. -/
example {Player : Type*} [DecidableEq Player] [Fintype Player] :
    ∃! φ : CoopGame Player →ₗ[ℝ] (Player → ℝ),
      IsEfficient φ ∧ IsSymmetric φ ∧ SatisfiesNullPlayerAxiom φ :=
  shapley_characterization

/-- Boundary check: on a one-player type, efficiency pins the allocation. -/
example : ∀ φ : CoopGame (Fin 1) →ₗ[ℝ] ((Fin 1) → ℝ),
    IsEfficient φ →
    ∀ v : CoopGame (Fin 1), φ v 0 = v.charFun Set.univ := by
  intro φ heff v
  simpa using heff v

/-- Boundary check: a null player gets zero from the characterized value. -/
example (v : CoopGame (Fin 2)) (i : Fin 2) (hnull : IsNullPlayer v i) :
    ∃! φ : CoopGame (Fin 2) →ₗ[ℝ] ((Fin 2) → ℝ),
      IsEfficient φ ∧ IsSymmetric φ ∧ SatisfiesNullPlayerAxiom φ ∧ φ v i = 0 := by
  obtain ⟨φ, ⟨heff, hsymm, hnull_ax⟩, huniq⟩ := shapley_characterization (Player := Fin 2)
  refine ⟨φ, ⟨heff, hsymm, hnull_ax, hnull_ax v i hnull⟩, ?_⟩
  intro ψ hψ
  exact huniq ψ ⟨hψ.1, hψ.2.1, hψ.2.2.1⟩

end MathlibExt.GameTheory.ShapleyValue
