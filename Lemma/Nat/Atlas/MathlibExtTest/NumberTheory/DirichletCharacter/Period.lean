import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.NumberTheory.DirichletCharacter.Period
open MonoidHom


/--
[one_period](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/Period.lean)
-/
@[path]
private lemma one_period :
  Function.Periodic (1 : ℤ →* ℂ) ((1 : ℕ) : ℤ) :=
  fun x => by simp

/--
[one_map_min](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/Period.lean)
-/
@[path]
private lemma one_map_min : ∀ d : ℕ, 0 < d →
  Function.Periodic (1 : ℤ →* ℂ) (d : ℤ) → 1 ≤ d :=
  fun _ hd _ => hd


-- created on 2026-10-23
