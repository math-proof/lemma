import Mathlib
import sympy.Basic
import Theorem.Analysis.NormedSpace.GrothendieckInequality.Part5

open scoped InnerProductSpace

/--
[GrothendieckInequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/GrothendieckInequality.lean)
-/
@[path]
private lemma grothendieck_inequality_real_eq :
-- imply
  ∃ K : ℝ, 0 < K ∧
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (x : Fin m → H) (y : Fin n → H),
      (∀ i, ‖x i‖ ≤ 1) → (∀ j, ‖y j‖ ≤ 1) →
      ∃ (ε : Fin m → ℝ) (δ : Fin n → ℝ),
        (∀ i, ε i = 1 ∨ ε i = -1) ∧
        (∀ j, δ j = 1 ∨ δ j = -1) ∧
        |∑ i : Fin m, ∑ j : Fin n, A i j * ⟪x i, y j⟫_ℝ| ≤
          K * |∑ i : Fin m, ∑ j : Fin n, A i j * ε i * δ j| := by
-- proof
  apply FunctionalAnalysis.GrothendieckInequalityWanted.grothendieck_inequality_real

-- created on 2026-10-10
