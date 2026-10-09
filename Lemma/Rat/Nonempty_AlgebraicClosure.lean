import Mathlib
import sympy.Basic


/--
[AlgebraicClosure_nonempty_algHom_rat_padicAlgClosure](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicClosure_nonempty_algHom_rat_padicAlgClosure.lean)
-/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime] :
-- imply
  Nonempty (AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]) := by
-- proof
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    (AlgebraicClosure.instIsAlgClosure ℚ).isAlgebraic
  exact ⟨IsAlgClosed.lift⟩


-- created on 2026-10-03
