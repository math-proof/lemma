import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.ModularCurve.DegeneracyTower
import Lemma.Int.P2MUtil

open ModularCurve AlgebraicCurve

/--
[ModularCurve_towerInclBar_surjective_of_dvd_dvd](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_towerInclBar_surjective_of_dvd_dvd.lean)
-/
@[path]
private lemma main
  [Field L] [Algebra ℚ L]
  {N M : ℕ} [NeZero N] [NeZero M]
-- given
  (h : N ∣ M)
  (h' : M ∣ N) :
-- imply
  Function.Surjective (towerInclBar L h) := by
-- proof
  intro y
  refine ⟨towerInclBar L h' y, ?_⟩
  have e := congrArg (fun f => f y) (towerInclBar_comp_towerInclBar L h' h (dvd_refl M))
  simpa only [AlgHom.comp_apply, towerInclBar_self] using e


-- created on 2026-10-23
