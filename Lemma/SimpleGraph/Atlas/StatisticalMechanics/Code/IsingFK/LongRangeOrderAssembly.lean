import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.IsingFK.LongRangeOrderAssembly
open StatMech StatMech.IsingFK


/--
[longRangeOrder_across_critical_of_fk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/LongRangeOrderAssembly.lean)
-/
@[path]
private lemma longRangeOrder_across_critical_of_fk_eq
  {d : ℕ}
  {corr : ℝ → Site d → ℝ}
  {tau : ℝ → Site d → ℝ}
  {pMap : ℝ → ℝ}
  {scale pc betaC : ℝ}
-- given
  (hscale : 0 < scale)
  (hcorr : ∀ beta x, corr beta x = scale * tau (pMap beta) x)
  (habove : ∀ {beta}, betaC < beta → pc < pMap beta)
  (hbelow : ∀ {beta}, beta < betaC → pMap beta < pc)
  (hsuper : ∀ {p}, pc < p → ∃ c : ℝ, 0 < c ∧ ∀ x : Site d, c ≤ tau p x)
  (hsub : ∀ {p}, p < pc → ∀ epsilon : ℝ, 0 < epsilon → ∃ n : ℕ, ∀ x : Site d, x ∉ box d n → tau p x < epsilon) :
-- imply
  (∀ {beta}, betaC < beta → HasLongRangeOrder corr beta) ∧ (∀ {beta}, beta < betaC → HasSpatialDecay corr beta) := by
-- proof
  apply StatMech.IsingFK.longRangeOrder_across_critical_of_fk corr tau pMap scale pc betaC hscale hcorr habove hbelow hsuper hsub


-- created on 2026-10-23
