import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.MonotoneOSSSAssembly
open MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptDisintegration


/--
[osss_onestep_cov_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotoneOSSSAssembly.lean)
-/
@[path]
private lemma osss_onestep_cov_bound_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  AdaptStepCovBound μ σ f := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.osss_onestep_cov_bound hpos hμ1 hmono σ hf hf0 hf1

/--
[osss_monotone_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotoneOSSSAssembly.lean)
-/
@[path]
private lemma osss_monotone_sharp_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  Lindeberg.var μ f ≤ ∑ e, revealAdapt μ σ f e * Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.osss_monotone_sharp hpos hμ1 hmono σ hf hf0 hf1

/--
[osss_fk_q2_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotoneOSSSAssembly.lean)
-/
@[path]
private lemma osss_fk_q2_sharp_eq
  [Fintype E]
  [DecidableEq E]
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
  Lindeberg.var (fkMass G p 2) f ≤ ∑ e, revealAdapt (fkMass G p 2) σ f e * Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.osss_fk_q2_sharp G hp hp1 σ hf hf0 hf1


-- created on 2026-10-23
