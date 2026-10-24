import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.PoincareApp
open Finset StatMech StatMech.OSSS StatMech.OSSS.PoincareApp StatMech.OSSS.MonotonicFK


/--
[var_eq_theta_mul_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PoincareApp.lean)
-/
@[path]
private lemma var_eq_theta_mul_one_sub_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hf : ∀ ω, f ω = 0 ∨ f ω = 1) :
-- imply
  Lindeberg.var μ f = Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) := by
-- proof
  apply StatMech.OSSS.PoincareApp.var_eq_theta_mul_one_sub μ f hf

/--
[indicator_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PoincareApp.lean)
-/
@[path]
private lemma indicator_zero_or_one_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  A.indicator (fun _ => (1 : ℝ)) ω = 0 ∨ A.indicator (fun _ => (1 : ℝ)) ω = 1 := by
-- proof
  apply StatMech.OSSS.PoincareApp.indicator_zero_or_one A ω

/--
[var_indicator_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PoincareApp.lean)
-/
@[path]
private lemma var_indicator_eq_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {A : Set (ConfigSpace E)} :
-- imply
  Lindeberg.var μ (A.indicator (fun _ => (1 : ℝ))) = Lindeberg.mean μ (A.indicator (fun _ => (1 : ℝ))) * (1 - Lindeberg.mean μ (A.indicator (fun _ => (1 : ℝ)))) := by
-- proof
  apply StatMech.OSSS.PoincareApp.var_indicator_eq μ A

/--
[poincare_covSum_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PoincareApp.lean)
-/
@[path]
private lemma poincare_covSum_ge_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hf : Monotone f)
  (hf01 : ∀ ω, f ω = 0 ∨ f ω = 1) :
-- imply
  Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.PoincareApp.poincare_covSum_ge hpos hμ1 hFKG hf hf01

/--
[poincare_covSum_indicator_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PoincareApp.lean)
-/
@[path]
private lemma poincare_covSum_indicator_ge_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hA : IsIncreasing A) :
-- imply
  Lindeberg.mean μ (A.indicator (fun _ => (1 : ℝ))) * (1 - Lindeberg.mean μ (A.indicator (fun _ => (1 : ℝ)))) ≤ ∑ e, Lindeberg.cov μ (A.indicator (fun _ => (1 : ℝ))) (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.PoincareApp.poincare_covSum_indicator_ge hpos hμ1 hFKG hA

/--
[lindebergMean_fkMass_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PoincareApp.lean)
-/
@[path]
private lemma lindebergMean_fkMass_indicator_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))} :
-- imply
  Lindeberg.mean (fkMass G p q) (A.indicator (fun _ => (1 : ℝ))) = FK.fkProbOf G p q A := by
-- proof
  apply StatMech.OSSS.MonotonicFK.lindebergMean_fkMass_indicator G p q A

/--
[lindebergCov_fkMass_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PoincareApp.lean)
-/
@[path]
private lemma lindebergCov_fkMass_coord_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
  {e : Sym2 V} :
-- imply
  Lindeberg.cov (fkMass G p q) (A.indicator (fun _ => (1 : ℝ))) (Lindeberg.coord e) = FK.fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) := by
-- proof
  apply StatMech.OSSS.MonotonicFK.lindebergCov_fkMass_coord G p q A e

/--
[fk_poincare_covSum_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PoincareApp.lean)
-/
@[path]
private lemma fk_poincare_covSum_ge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  FK.fkProbOf G p q A * (1 - FK.fkProbOf G p q A) ≤ ∑ e, FK.fkCov G p q (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) := by
-- proof
  apply StatMech.OSSS.MonotonicFK.fk_poincare_covSum_ge G hp hp1 hq hA


-- created on 2026-10-23
