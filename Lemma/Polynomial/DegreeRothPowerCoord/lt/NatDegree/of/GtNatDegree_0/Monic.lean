import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPowerCoord_degree_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (g : ℤ[X])
  (n : ℕ)
-- given
  (hd : 0 < g.natDegree)
  (hg : g.Monic) :
-- imply
  (rothPowerCoord g n).degree < g.natDegree := by
-- proof
  induction n with
  | zero =>
    rw [rothPowerCoord, degree_one]
    exact WithBot.coe_pos.mpr hd
  | succ n ih =>
    rw [degree_lt_iff_coeff_zero]
    intro k hk
    cases k with
    | zero => omega
    | succ k =>
      rw [rothPowerCoord, coeff_sub, coeff_X_mul, coeff_C_mul]
      if heq : k + 1 = g.natDegree then
        have hkpred : k = g.natDegree - 1 := by omega
        have hdsub : g.natDegree - 1 + 1 = g.natDegree := by omega
        rw [hkpred, hdsub, hg.coeff_natDegree]
        ring
      else
        have hgt : g.natDegree < k + 1 := lt_of_le_of_ne hk (Ne.symm heq)
        have hku : g.natDegree ≤ k := by omega
        rw [(degree_lt_iff_coeff_zero _ _).mp ih k hku,
          coeff_eq_zero_of_natDegree_lt hgt]
        ring


-- created on 2026-10-21
