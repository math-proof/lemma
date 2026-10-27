import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.AlgebraicCurve_PlaceTaylorCoeff
import Lemma.Int.P2MUtil

open AlgebraicCurve AlgebraicCurve.Place

/--
[AlgebraicCurve_Place_taylorRem_succ_eq_taylorRem_taylorRem_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_taylorRem_succ_eq_taylorRem_taylorRem_one.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {v : Place K F}
  {t f : F}
  {r : ℕ} :
-- imply
  taylorRem v t f (r + 1) = taylorRem v t (taylorRem v t f 1) r := by
-- proof
  induction r with
    | zero => rfl
    | succ r ih => rw [taylorRem_succ, ih, ← taylorRem_succ]


-- created on 2026-10-23
