import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.IsingFK.EsInfinite.Part2
open MeasureTheory Filter Topology BoundedContinuousFunction StatMech StatMech.IsingFK


/--
[tendsto_eq_of_eq_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsInfinite.lean)
-/
@[path]
private lemma tendsto_eq_of_eq_of_tendsto_eq
  {d : ℕ}
  {a b : ℕ → ℝ}
  {A B : ℝ}
-- given
  (hab : ∀ n, a n = b n)
  (ha : Tendsto a atTop (𝓝 A))
  (hb : Tendsto b atTop (𝓝 B)) :
-- imply
  A = B := by
-- proof
  apply StatMech.IsingFK.tendsto_eq_of_eq_of_tendsto hab ha hb

/--
[magnetization_eq_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsInfinite.lean)
-/
@[path]
private lemma magnetization_eq_limit_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ} :
-- imply
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => fvMagnetization d β (φ n)) atTop (𝓝 (magnetization d β)) := by
-- proof
  apply StatMech.IsingFK.magnetization_eq_limit d β

/--
[magPercoId_of_fvES_of_fkLim](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsInfinite.lean)
-/
@[path]
private lemma magPercoId_of_fvES_of_fkLim_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {p : ℝ}
  {fvBoundaryConn : ℕ → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : (0 : ℝ) < 2)
  (hfvES : ∀ n, fvMagnetization d β n = fvBoundaryConn n)
  (hfkLim : Tendsto fvBoundaryConn atTop (𝓝 (FK.fkTheta d hp hp1 hq (q := 2)))) :
-- imply
  magnetization d β = FK.fkTheta d hp hp1 hq (q := 2) := by
-- proof
  apply StatMech.IsingFK.magPercoId_of_fvES_of_fkLim d β hp hp1 hq fvBoundaryConn hfvES hfkLim

/--
[magPercoId_of_fvES_of_fkLim_hyp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsInfinite.lean)
-/
@[path]
private lemma magPercoId_of_fvES_of_fkLim_hyp_eq
  {d : ℕ}
  {d : ℕ}
  {fvBoundaryConn : ℝ → ℕ → ℝ}
-- given
  (hfvES : ∀ β, 0 < β → ∀ n, fvMagnetization d β n = fvBoundaryConn β n)
  (hfkLim : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), Tendsto (fvBoundaryConn β) atTop (𝓝 (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)))) :
-- imply
  ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1), magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) := by
-- proof
  apply StatMech.IsingFK.magPercoId_of_fvES_of_fkLim_hyp d fvBoundaryConn hfvES hfkLim


-- created on 2026-10-23
