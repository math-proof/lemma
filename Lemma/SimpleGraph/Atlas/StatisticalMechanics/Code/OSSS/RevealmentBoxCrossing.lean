import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentBoxCrossing.Part3
open MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.RevealmentBoxCrossing


/--
[truncInd_eq_truncIndC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoxCrossing.lean)
-/
@[path]
private lemma truncInd_eq_truncIndC_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {U : Fin n → ℝ}
  {t : ℕ} :
-- imply
  truncInd μ σ f U t = truncIndC σ f (codeMap μ (σ : Fin n → E) U) t := by
-- proof
  apply StatMech.OSSS.RevealmentBoxCrossing.truncInd_eq_truncIndC μ σ f U t

/--
[truncIndC_succ_eq_reachInd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoxCrossing.lean)
-/
@[path]
private lemma truncIndC_succ_eq_reachInd_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {X : ConfigSpace E}
  {i : ℕ} :
-- imply
  truncIndC σ f X (i + 1) = reachInd σ f i X := by
-- proof
  apply StatMech.OSSS.RevealmentBoxCrossing.truncIndC_succ_eq_reachInd σ f X i

/--
[revealAdapt_eq_truncSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoxCrossing.lean)
-/
@[path]
private lemma revealAdapt_eq_truncSum_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  revealAdapt μ σ f e = ∑ X, truncIndC σ f X ((σ.symm e : ℕ) + 1) * μ X := by
-- proof
  apply StatMech.OSSS.RevealmentBoxCrossing.revealAdapt_eq_truncSum μ hpos hμ1 σ f e

/--
[revealAdapt_eq_reachProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoxCrossing.lean)
-/
@[path]
private lemma revealAdapt_eq_reachProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  revealAdapt μ σ f e = reachProb μ σ f e := by
-- proof
  apply StatMech.OSSS.RevealmentBoxCrossing.revealAdapt_eq_reachProb hpos hμ1 σ f e

/--
[reachProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoxCrossing.lean)
-/
@[path]
private lemma reachProb_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  0 ≤ reachProb μ σ f e := by
-- proof
  apply StatMech.OSSS.RevealmentBoxCrossing.reachProb_nonneg hpos σ f e

/--
[reachProb_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoxCrossing.lean)
-/
@[path]
private lemma reachProb_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  reachProb μ σ f e ≤ 1 := by
-- proof
  apply StatMech.OSSS.RevealmentBoxCrossing.reachProb_le_one hpos hμ1 σ f e

/--
[revealAdapt_le_reachProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoxCrossing.lean)
-/
@[path]
private lemma revealAdapt_le_reachProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  revealAdapt μ σ f e ≤ reachProb μ σ f e := by
-- proof
  apply StatMech.OSSS.RevealmentBoxCrossing.revealAdapt_le_reachProb hpos hμ1 σ f e

/--
[revealAdapt_le_of_reachProb_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoxCrossing.lean)
-/
@[path]
private lemma revealAdapt_le_of_reachProb_le_eq
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
  (hreach : ∀ e, reachProb μ σ f e ≤ D) :
-- imply
  ∀ e, revealAdapt μ σ f e ≤ D := by
-- proof
  apply StatMech.OSSS.RevealmentBoxCrossing.revealAdapt_le_of_reachProb_le hpos hμ1 σ f hreach

/--
[os_cov_lower_bound_from_reachBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoxCrossing.lean)
-/
@[path]
private lemma os_cov_lower_bound_from_reachBound_eq
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
  (hreach : ∀ e, reachProb μ σ f e ≤ D) :
-- imply
  Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) / D ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.RevealmentBoxCrossing.os_cov_lower_bound_from_reachBound hpos hμ1 hFKG hmono σ hf hf0 hf1 hidem D hDpos hreach

/--
[os_cov_lower_bound_reach_poincare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoxCrossing.lean)
-/
@[path]
private lemma os_cov_lower_bound_reach_poincare_eq
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
  apply StatMech.OSSS.RevealmentBoxCrossing.os_cov_lower_bound_reach_poincare hpos hμ1 hFKG hmono σ hf hf0 hf1 hidem


-- created on 2026-10-23
