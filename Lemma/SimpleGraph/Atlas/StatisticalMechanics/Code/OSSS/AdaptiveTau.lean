import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
open Finset MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptiveTau


/--
[Vcube_eq_cube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveTau.lean)
-/
@[path]
private lemma Vcube_eq_cube_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ} :
-- imply
  Vcube n = cube n := by
-- proof
  apply StatMech.OSSS.AdaptiveTau.Vcube_eq_cube n

/--
[measurable_f_codeMap_Wt_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveTau.lean)
-/
@[path]
private lemma measurable_f_codeMap_Wt_fiber_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {U : Fin n → ℝ}
  {s : ℕ} :
-- imply
  Measurable (fun V : Fin n → ℝ => f (codeMap μ (σ : Fin n → E) (Wt U V s))) := by
-- proof
  apply StatMech.OSSS.AdaptiveTau.measurable_f_codeMap_Wt_fiber μ σ f U s

/--
[integrable_prod_obs_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveTau.lean)
-/
@[path]
private lemma integrable_prod_obs_fiber_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {e : E}
  {U : Fin n → ℝ}
  {s₁ s₂ : ℕ}
-- given
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  Integrable (fun V : Fin n → ℝ => f (codeMap μ (σ : Fin n → E) (Wt U V s₁)) * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s₂))) (Vcube n) := by
-- proof
  apply StatMech.OSSS.AdaptiveTau.integrable_prod_obs_fiber μ σ hfC e U s₁ s₂

/--
[grandCoupling_fkg_cross_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveTau.lean)
-/
@[path]
private lemma grandCoupling_fkg_cross_fiber_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {e : E}
  {s₁ s₂ : ℕ}
  {U : Fin n → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V s₁)) ∂(Vcube n)) * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s₂)) ∂(Vcube n)) ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V s₁)) * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s₂)) ∂(Vcube n) := by
-- proof
  apply StatMech.OSSS.AdaptiveTau.grandCoupling_fkg_cross_fiber hpos hmono σ hf hfC e s₁ s₂ U

/--
[osss_grand_coupling_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveTau.lean)
-/
@[path]
private lemma osss_grand_coupling_fiber_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {e : E}
  {t : ℕ}
  {U : Fin n → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  ((∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) ∂(Vcube n)) * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n)) ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n)) ∧ ((∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n)) * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) ∂(Vcube n)) ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t)) * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) ∂(Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptiveTau.osss_grand_coupling_fiber hpos hmono σ hf hfC e t U

/--
[abs_step_integral_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveTau.lean)
-/
@[path]
private lemma abs_step_integral_fiber_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {t : ℕ}
  {U : Fin n → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf)
  (ht : 1 ≤ t)
  (htn : t - 1 < n) :
-- imply
  (∫ V, |f (codeMap μ (σ : Fin n → E) (Wt U V t)) - f (codeMap μ (σ : Fin n → E) (Wt U V (t-1)))| ∂(Vcube n)) = (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) ∂(Vcube n)) + (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t)) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n)) - (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n)) - (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t)) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) ∂(Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptiveTau.abs_step_integral_fiber hpos hmono σ hf hfC t ht htn U

/--
[step_fiber_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveTau.lean)
-/
@[path]
private lemma step_fiber_le_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {t : ℕ}
  {U : Fin n → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf)
  (ht : 1 ≤ t)
  (htn : t - 1 < n) :
-- imply
  (∫ V, |f (codeMap μ (σ : Fin n → E) (Wt U V t)) - f (codeMap μ (σ : Fin n → E) (Wt U V (t-1)))| ∂(Vcube n)) ≤ (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) ∂(Vcube n)) + (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t)) * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n)) - (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) ∂(Vcube n)) * (∫ V, Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n)) - (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n)) * (∫ V, Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) ∂(Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptiveTau.step_fiber_le hpos hmono σ hf hfC t ht htn U

/--
[integral_U_diagonal_eq_bbb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveTau.lean)
-/
@[path]
private lemma integral_U_diagonal_eq_bbb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {e : E}
  {s : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  (∫ U, (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V s)) * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s)) ∂(Vcube n)) ∂(Vcube n)) = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) := by
-- proof
  apply StatMech.OSSS.AdaptiveTau.integral_U_diagonal_eq_bbb hpos hμ1 σ hfC e s

/--
[integral_U_cross_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveTau.lean)
-/
@[path]
private lemma integral_U_cross_le_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {e : E}
  {s₁ s₂ : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  (∫ U, (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V s₁)) ∂(Vcube n)) * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s₂)) ∂(Vcube n)) ∂(Vcube n)) ≤ ∫ p, f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₁)) * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₂)) ∂((Vcube n).prod (Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptiveTau.integral_U_cross_le hpos hmono σ hf hfC e s₁ s₂

/--
[tree_osss](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveTau.lean)
-/
@[path]
private lemma tree_osss_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hStep : StepCovBoundTwo μ T (T.evalR)) :
-- imply
  Lindeberg.var μ (T.evalR) ≤ ∑ e, revealmentMu μ T e * Lindeberg.cov μ (T.evalR) (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptiveTau.tree_osss hpos hμ1 T hStep

/--
[fk_q2_osss_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveTau.lean)
-/
@[path]
private lemma fk_q2_osss_sharp_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {T : DecisionTree (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hStep : StepCovBoundTwo (fkMass G p 2) T (T.evalR)) :
-- imply
  Lindeberg.var (fkMass G p 2) (T.evalR) ≤ ∑ e, revealmentMu (fkMass G p 2) T e * Lindeberg.cov (fkMass G p 2) (T.evalR) (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptiveTau.fk_q2_osss_sharp G hp hp1 T hStep


-- created on 2026-10-23
