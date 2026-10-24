import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_ModularUnit
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_eisensteinNumerator_coprime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_eisensteinNumerator_coprime.lean)
-/
@[path]
private lemma main
  {p : ℕ}
-- given
  (hp : p ≠ 0) :
-- imply
  (eisensteinNumerator p).Coprime p := by
-- proof
  refine Nat.Coprime.coprime_dvd_left (eisensteinNumerator_dvd p) ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  rw [Nat.succ_sub_one, Nat.succ_eq_add_one]
  exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right k)


-- created on 2026-10-23
