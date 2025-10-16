import sympy.functions.elementary.complexes
import Lemma.Algebra.Square.eq.Mul
open Algebra


@[main]
private lemma main
  {z : ℂ} :
-- imply
  ‖z‖ = √((re z)² + (im z)²) := by
-- proof
  rw [Square.eq.Mul, Square.eq.Mul]
  rw [← Complex.normSq_apply]
  exact rfl




-- created on 2025-01-16
-- updated on 2025-01-17
