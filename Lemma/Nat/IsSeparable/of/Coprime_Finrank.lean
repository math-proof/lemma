import Mathlib
import sympy.Basic


/--
[Algebra_IsSeparable_of_coprime_finrank_expChar](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_IsSeparable_of_coprime_finrank_expChar.lean)
-/
@[path]
private lemma main
  {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {q : ℕ} [ExpChar F q]
-- given
  (h : Nat.Coprime (Module.finrank F E) q) :
-- imply
  Algebra.IsSeparable F E := by
-- proof
  rw [← Field.finSepDegree_eq_finrank_iff]

  have : ExpChar (separableClosure F E) q :=
    expChar_of_injective_algebraMap (algebraMap F (separableClosure F E)).injective q
  have : IsPurelyInseparable (separableClosure F E) E := separableClosure.isPurelyInseparable F E
  obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow (separableClosure F E) E q
  have hins : Field.finInsepDegree F E = q ^ n := hn
  have hmul := Field.finSepDegree_mul_finInsepDegree F E
  rw [hins] at hmul

  have hdvd : q ^ n ∣ Module.finrank F E := ⟨Field.finSepDegree F E, by rw [mul_comm]; exact hmul.symm⟩
  have hone : q ^ n = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left n h.symm) hdvd
  rw [hone, mul_one] at hmul
  exact hmul


-- created on 2026-10-05
