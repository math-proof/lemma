import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FamilyEqzzzResolution
open MeasureTheory Filter Topology StatMech StatMech.OSSS StatMech.OSSS.FamilyEqzzzResolution


/--
[adaptiveFamilyOSSS_of_causal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FamilyEqzzzResolution.lean)
-/
@[path]
private lemma adaptiveFamilyOSSS_of_causal_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {Tf : κ → DecisionTree E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hf : Monotone f)
  (hTf : ∀ k, (Tf k).evalR = f) :
-- imply
  AdaptiveFamilyOSSS (μ := μ) Tf f := by
-- proof
  apply StatMech.OSSS.FamilyEqzzzResolution.adaptiveFamilyOSSS_of_causal hpos hμ1 hFKG Tf hf hTf

/--
[bareAdaptiveFamilyOSSS_not_arbitrary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FamilyEqzzzResolution.lean)
-/
@[path]
private lemma bareAdaptiveFamilyOSSS_not_arbitrary_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ¬ BareAdaptiveFamilyOSSS (μ := StepCov.Counterexample.muU) (fun _ : Unit => DecisionTree.leaf false) (Lindeberg.coord false) := by
-- proof
  apply StatMech.OSSS.FamilyEqzzzResolution.bareAdaptiveFamilyOSSS_not_arbitrary

/--
[var_le_avg_adaptive_reveal_mul_sum_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FamilyEqzzzResolution.lean)
-/
@[path]
private lemma var_le_avg_adaptive_reveal_mul_sum_cov_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  [Fintype κ]
  [Nonempty κ]
  {Tf : κ → DecisionTree E}
  {f : ConfigSpace E → ℝ}
  {D : ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hf : Monotone f)
  (hOSSS : AdaptiveFamilyOSSS (μ := μ) Tf f)
  (hD : ∀ e, (1 / (Fintype.card κ : ℝ)) * ∑ k, revealmentMu μ (Tf k) e ≤ D) :
-- imply
  Lindeberg.var μ f ≤ D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.FamilyEqzzzResolution.var_le_avg_adaptive_reveal_mul_sum_cov hpos hμ1 hFKG Tf hf hOSSS D hD

/--
[var_le_avg_adaptive_reveal_mul_sum_cov_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FamilyEqzzzResolution.lean)
-/
@[path]
private lemma var_le_avg_adaptive_reveal_mul_sum_cov_unconditional_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  [Fintype κ]
  [Nonempty κ]
  {Tf : κ → DecisionTree E}
  {f : ConfigSpace E → ℝ}
  {D : ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hf : Monotone f)
  (hTf : ∀ k, (Tf k).evalR = f)
  (hD : ∀ e, (1 / (Fintype.card κ : ℝ)) * ∑ k, revealmentMu μ (Tf k) e ≤ D) :
-- imply
  Lindeberg.var μ f ≤ D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.FamilyEqzzzResolution.var_le_avg_adaptive_reveal_mul_sum_cov_unconditional hpos hμ1 hFKG Tf hf hTf D hD

/--
[fk_q2_cov_lower_bound_of_adaptive_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FamilyEqzzzResolution.lean)
-/
@[path]
private lemma fk_q2_cov_lower_bound_of_adaptive_family_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {p : ℝ}
  [Fintype κ]
  [Nonempty κ]
  {Tf : κ → DecisionTree (Sym2 W)}
  {f : ConfigSpace (Sym2 W) → ℝ}
  {R : κ → Sym2 W → ℝ}
  {D : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hf : Monotone f)
  (hidem : ∀ ω, f ω * f ω = f ω)
  (hOSSS : AdaptiveFamilyOSSS (μ := fkMass G p 2) Tf f)
  (hDpos : 0 < D)
  (hreach : ∀ k e, revealmentMu (fkMass G p 2) (Tf k) e ≤ R k e)
  (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
-- imply
  Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f) / D ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.FamilyEqzzzResolution.fk_q2_cov_lower_bound_of_adaptive_family G hp hp1 Tf hf hidem hOSSS R D hDpos hreach hsum

/--
[fk_q2_cov_lower_bound_of_adaptive_family_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FamilyEqzzzResolution.lean)
-/
@[path]
private lemma fk_q2_cov_lower_bound_of_adaptive_family_unconditional_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {p : ℝ}
  [Fintype κ]
  [Nonempty κ]
  {Tf : κ → DecisionTree (Sym2 W)}
  {f : ConfigSpace (Sym2 W) → ℝ}
  {R : κ → Sym2 W → ℝ}
  {D : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hf : Monotone f)
  (hidem : ∀ ω, f ω * f ω = f ω)
  (hTf : ∀ k, (Tf k).evalR = f)
  (hDpos : 0 < D)
  (hreach : ∀ k e, revealmentMu (fkMass G p 2) (Tf k) e ≤ R k e)
  (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
-- imply
  Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f) / D ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.FamilyEqzzzResolution.fk_q2_cov_lower_bound_of_adaptive_family_unconditional G hp hp1 Tf hf hidem hTf R D hDpos hreach hsum

/--
[wired_box_theta_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FamilyEqzzzResolution.lean)
-/
@[path]
private lemma wired_box_theta_tendsto_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun n => IsingFK.boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n) atTop (nhds (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))) := by
-- proof
  apply StatMech.OSSS.FamilyEqzzzResolution.wired_box_theta_tendsto hp hp1


-- created on 2026-10-23
