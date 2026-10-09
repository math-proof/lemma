import Mathlib
import sympy.Basic


/--
[Matrix_natCard_GL_fin_two_zmod_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_natCard_GL_fin_two_zmod_eq.lean)
-/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime] :
-- imply
  Nat.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
-- proof
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]


-- created on 2026-10-03
