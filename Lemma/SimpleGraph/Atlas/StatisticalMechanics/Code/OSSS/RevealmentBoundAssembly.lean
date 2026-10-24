import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.RevealmentBoundAssembly
open MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.RevealmentBoundAssembly


/--
[revealAdapt_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoundAssembly.lean)
-/
@[path]
private lemma revealAdapt_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E} :
-- imply
  0 ≤ revealAdapt μ σ f e := by
-- proof
  apply StatMech.OSSS.RevealmentBoundAssembly.revealAdapt_nonneg μ σ f e

/--
[revealAdapt_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoundAssembly.lean)
-/
@[path]
private lemma revealAdapt_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E} :
-- imply
  revealAdapt μ σ f e ≤ 1 := by
-- proof
  apply StatMech.OSSS.RevealmentBoundAssembly.revealAdapt_le_one μ σ f e

/--
[var_eq_theta_one_sub_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoundAssembly.lean)
-/
@[path]
private lemma var_eq_theta_one_sub_theta_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hidem : ∀ ω, f ω * f ω = f ω) :
-- imply
  Lindeberg.var μ f = Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) := by
-- proof
  apply StatMech.OSSS.RevealmentBoundAssembly.var_eq_theta_one_sub_theta hidem

/--
[indicator_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoundAssembly.lean)
-/
@[path]
private lemma indicator_idem_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  A.indicator (fun _ => (1 : ℝ)) ω * A.indicator (fun _ => (1 : ℝ)) ω = A.indicator (fun _ => (1 : ℝ)) ω := by
-- proof
  apply StatMech.OSSS.RevealmentBoundAssembly.indicator_idem A ω

/--
[var_le_revealBound_mul_sum_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoundAssembly.lean)
-/
@[path]
private lemma var_le_revealBound_mul_sum_cov_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {D : ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1)
  (hD : ∀ e, revealAdapt μ σ f e ≤ D) :
-- imply
  Lindeberg.var μ f ≤ D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.RevealmentBoundAssembly.var_le_revealBound_mul_sum_cov hpos hμ1 hFKG hmono σ hf hf0 hf1 D hD

/--
[os_cov_lower_bound_assembled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoundAssembly.lean)
-/
@[path]
private lemma os_cov_lower_bound_assembled_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {D : ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1)
  (hidem : ∀ ω, f ω * f ω = f ω)
  (hDpos : 0 < D)
  (hD : ∀ e, revealAdapt μ σ f e ≤ D) :
-- imply
  Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) / D ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.RevealmentBoundAssembly.os_cov_lower_bound_assembled hpos hμ1 hFKG hmono σ hf hf0 hf1 hidem D hDpos hD

/--
[os_cov_lower_bound_assembled_fk_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoundAssembly.lean)
-/
@[path]
private lemma os_cov_lower_bound_assembled_fk_q2_eq
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
  {D : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1)
  (hidem : ∀ ω, f ω * f ω = f ω)
  (hDpos : 0 < D)
  (hD : ∀ e, revealAdapt (fkMass G p 2) σ f e ≤ D) :
-- imply
  Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f) / D ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.RevealmentBoundAssembly.os_cov_lower_bound_assembled_fk_q2 G hp hp1 σ hf hf0 hf1 hidem D hDpos hD

/--
[os_cov_lower_bound_poincare_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoundAssembly.lean)
-/
@[path]
private lemma os_cov_lower_bound_poincare_witness_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1)
  (hidem : ∀ ω, f ω * f ω = f ω) :
-- imply
  Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.RevealmentBoundAssembly.os_cov_lower_bound_poincare_witness hpos hμ1 hFKG hmono σ hf hf0 hf1 hidem


-- created on 2026-10-23
