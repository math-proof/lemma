import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKRevealmentClose
open MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.FKRevealmentClose


/--
[var_le_avg_reveal_mul_sum_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKRevealmentClose.lean)
-/
@[path]
private lemma var_le_avg_reveal_mul_sum_cov_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  [Fintype κ]
  [Nonempty κ]
  {m : ℕ}
  {σf : κ → (Fin m ≃ E)}
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
  (hD : ∀ e, (1 / (Fintype.card κ : ℝ)) * ∑ k, revealAdapt μ (σf k) f e ≤ D) :
-- imply
  Lindeberg.var μ f ≤ D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.FKRevealmentClose.var_le_avg_reveal_mul_sum_cov hpos hμ1 hFKG hmono σf hf hf0 hf1 D hD

/--
[fk_os_cov_lower_bound_avg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKRevealmentClose.lean)
-/
@[path]
private lemma fk_os_cov_lower_bound_avg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  [Fintype κ]
  [Nonempty κ]
  {m : ℕ}
  {σf : κ → (Fin m ≃ E)}
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
  (hD : ∀ e, (1 / (Fintype.card κ : ℝ)) * ∑ k, revealAdapt μ (σf k) f e ≤ D) :
-- imply
  Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) / D ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.FKRevealmentClose.fk_os_cov_lower_bound_avg hpos hμ1 hFKG hmono σf hf hf0 hf1 hidem D hDpos hD

/--
[avg_reveal_le_of_perScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKRevealmentClose.lean)
-/
@[path]
private lemma avg_reveal_le_of_perScale_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  [Fintype κ]
  [Nonempty κ]
  {m : ℕ}
  {σf : κ → (Fin m ≃ E)}
  {f : ConfigSpace E → ℝ}
  {R : κ → E → ℝ}
  {D : ℝ}
-- given
  (hreach : ∀ k e, revealAdapt μ (σf k) f e ≤ R k e)
  (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
-- imply
  ∀ e, (1 / (Fintype.card κ : ℝ)) * ∑ k, revealAdapt μ (σf k) f e ≤ D := by
-- proof
  apply StatMech.OSSS.FKRevealmentClose.avg_reveal_le_of_perScale σf f R D hreach hsum

/--
[fk_os_cov_lower_bound_from_perScaleReveal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKRevealmentClose.lean)
-/
@[path]
private lemma fk_os_cov_lower_bound_from_perScaleReveal_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  [Fintype κ]
  [Nonempty κ]
  {m : ℕ}
  {σf : κ → (Fin m ≃ E)}
  {f : ConfigSpace E → ℝ}
  {R : κ → E → ℝ}
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
  (hreach : ∀ k e, revealAdapt μ (σf k) f e ≤ R k e)
  (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
-- imply
  Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) / D ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.FKRevealmentClose.fk_os_cov_lower_bound_from_perScaleReveal hpos hμ1 hFKG hmono σf hf hf0 hf1 hidem R D hDpos hreach hsum

/--
[revealAdapt_first_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKRevealmentClose.lean)
-/
@[path]
private lemma revealAdapt_first_eq_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (he : (σ.symm e : ℕ) = 0)
  (hnc : ∀ X, ¬ ∀ w, f w = f X) :
-- imply
  revealAdapt μ σ f e = 1 := by
-- proof
  apply StatMech.OSSS.FKRevealmentClose.revealAdapt_first_eq_one hpos hμ1 σ f e he hnc

/--
[revealAdapt_single_no_over_n](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKRevealmentClose.lean)
-/
@[path]
private lemma revealAdapt_single_no_over_n_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  {c : ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (he : (σ.symm e : ℕ) = 0)
  (hnc : ∀ X, ¬ ∀ w, f w = f X)
  (hc : c < 1) :
-- imply
  ¬ revealAdapt μ σ f e ≤ c := by
-- proof
  apply StatMech.OSSS.FKRevealmentClose.revealAdapt_single_no_over_n hpos hμ1 σ f e he hnc hc

/--
[revealAdapt_eq_one_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKRevealmentClose.lean)
-/
@[path]
private lemma revealAdapt_eq_one_witness_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  revealAdapt (fun _ : ConfigSpace (Fin 2) => 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ)) (Equiv.refl (Fin 2)) (Lindeberg.coord (0 : Fin 2)) (0 : Fin 2) = 1 := by
-- proof
  apply StatMech.OSSS.FKRevealmentClose.revealAdapt_eq_one_witness

/--
[avg_reveal_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKRevealmentClose.lean)
-/
@[path]
private lemma avg_reveal_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  [Fintype κ]
  [Nonempty κ]
  {m : ℕ}
  {σf : κ → (Fin m ≃ E)}
  {f : ConfigSpace E → ℝ}
  {e : E} :
-- imply
  (1 / (Fintype.card κ : ℝ)) * ∑ k, revealAdapt μ (σf k) f e ≤ 1 := by
-- proof
  apply StatMech.OSSS.FKRevealmentClose.avg_reveal_le_one σf f e

/--
[fk_os_cov_lower_bound_avg_poincare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKRevealmentClose.lean)
-/
@[path]
private lemma fk_os_cov_lower_bound_avg_poincare_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  [Fintype κ]
  [Nonempty κ]
  {m : ℕ}
  {σf : κ → (Fin m ≃ E)}
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
  apply StatMech.OSSS.FKRevealmentClose.fk_os_cov_lower_bound_avg_poincare hpos hμ1 hFKG hmono σf hf hf0 hf1 hidem

/--
[fk_q2_cov_lower_bound_from_perScaleReveal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKRevealmentClose.lean)
-/
@[path]
private lemma fk_q2_cov_lower_bound_from_perScaleReveal_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  [Fintype κ]
  [Nonempty κ]
  {m : ℕ}
  {σf : κ → (Fin m ≃ Sym2 V)}
  {f : ConfigSpace (Sym2 V) → ℝ}
  {R : κ → Sym2 V → ℝ}
  {D : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1)
  (hidem : ∀ ω, f ω * f ω = f ω)
  (hDpos : 0 < D)
  (hreach : ∀ k e, revealAdapt (fkMass G p 2) (σf k) f e ≤ R k e)
  (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
-- imply
  Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f) / D ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.FKRevealmentClose.fk_q2_cov_lower_bound_from_perScaleReveal G hp hp1 σf hf hf0 hf1 hidem R D hDpos hreach hsum


-- created on 2026-10-23
