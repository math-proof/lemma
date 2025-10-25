import sympy.core.numbers
import Lemma.Nat.Square.eq.Mul
open Nat


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  ‖x + I * y‖ = √(x² + y²) := by
-- proof
  dsimp [Norm.norm]
  simp [Complex.normSq]
  rw [Mul.eq.Square, Mul.eq.Square]

-- created on 2025-01-05
