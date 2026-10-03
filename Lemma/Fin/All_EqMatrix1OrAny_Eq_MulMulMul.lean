import Mathlib
import sympy.Basic


/--
[LanglandsTunnell_Artin_eq_one_or_eq_commutator_of_det_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LanglandsTunnell_Artin_eq_one_or_eq_commutator_of_det_eq_one.lean)
-/
@[main]
private lemma main
  :
-- imply
  ∀ g : GL (Fin 2) (ZMod 3), (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 →
    (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 ∨
      ∃ x : GL (Fin 2) (ZMod 3), ∃ y : GL (Fin 2) (ZMod 3), g = x * y * x⁻¹ * y⁻¹ := by
-- proof
  decide +kernel


-- created on 2026-10-03
