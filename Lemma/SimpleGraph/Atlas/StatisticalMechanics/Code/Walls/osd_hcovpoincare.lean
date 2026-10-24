import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.osd_hcovpoincare
open Finset StatMech StatMech.Walls


/--
[osd_hcovPoincare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_hcovpoincare.lean)
-/
@[path]
private lemma osd_hcovPoincare_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hA : IsIncreasing A) :
-- imply
  fkProbOf G p 2 A * (1 - fkProbOf G p 2 A) ≤ ∑ e, fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) := by
-- proof
  apply StatMech.Walls.osd_hcovPoincare G hp hp1 A hA

/--
[osd_hcovPoincare_var](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_hcovpoincare.lean)
-/
@[path]
private lemma osd_hcovPoincare_var_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  Lindeberg.var (fkMass G p 2) f ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
-- proof
  apply StatMech.Walls.osd_hcovPoincare_var G hp hp1 σ hf hf0 hf1

/--
[osd_hcovPoincare_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_hcovpoincare.lean)
-/
@[path]
private lemma osd_hcovPoincare_indicator_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hA : IsIncreasing A) :
-- imply
  Lindeberg.mean (fkMass G p 2) (A.indicator (fun _ => (1 : ℝ))) * (1 - Lindeberg.mean (fkMass G p 2) (A.indicator (fun _ => (1 : ℝ)))) ≤ ∑ e, Lindeberg.cov (fkMass G p 2) (A.indicator (fun _ => (1 : ℝ))) (Lindeberg.coord e) := by
-- proof
  apply StatMech.Walls.osd_hcovPoincare_indicator G hp hp1 σ A hA


-- created on 2026-10-23
