import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DirichletCharacter.Period
open MonoidHom


/--
[isDirichletCharacterModulus_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Period.lean)
-/
@[path]
private lemma isDirichletCharacterModulus_iff_eq
  [MonoidWithZero R] [Nontrivial R] [IsCancelMulZero R]
  {χ : ℤ →* R}
  {m m' : ℕ}
-- given
  (hm : 0 < m)
  (hper : Function.Periodic χ (m : ℤ))
  (hmin : ∀ d : ℕ, 0 < d → Function.Periodic χ (d : ℤ) → m ≤ d)
  (hm' : 0 < m') :
-- imply
  χ.IsDirichletCharacterModulus m' ↔ m ∣ m' ∧ ∃ k : ℕ, m' ∣ m ^ k := by
-- proof
  apply MonoidHom.isDirichletCharacterModulus_iff hm hper hmin hm'

/--
[isDirichletCharacterModulus_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Period.lean)
-/
@[path]
private lemma isDirichletCharacterModulus_self_eq
  [MonoidWithZero R] [Nontrivial R] [IsCancelMulZero R]
  {χ : ℤ →* R}
  {m : ℕ}
-- given
  (hm : 0 < m)
  (hper : Function.Periodic χ (m : ℤ))
  (hmin : ∀ d : ℕ, 0 < d → Function.Periodic χ (d : ℤ) → m ≤ d) :
-- imply
  χ.IsDirichletCharacterModulus m := by
-- proof
  apply MonoidHom.isDirichletCharacterModulus_self hm hper hmin


-- created on 2026-10-20
