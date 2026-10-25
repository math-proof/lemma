import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FrontierFamilyClose
open MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.FrontierFamilyClose


/--
[frf_familyFrontierConn_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FrontierFamilyClose.lean)
-/
@[path]
private lemma frf_familyFrontierConn_false_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {nE : ℕ}
  {σf : κ → (Fin nE ≃ E)}
  {f : ConfigSpace E → ℝ}
  {endU endV : E → V}
  {B : κ → Set V}
  {k₀ : κ}
  {e₀ : E}
  {X : ConfigSpace E}
-- given
  (he₀ : ((σf k₀).symm e₀ : ℕ) = 0)
  (hnc : ∃ w, f w ≠ f X)
  (hnotU : ¬ ConnOpenSet endU endV X (endU e₀) (B k₀))
  (hnotV : ¬ ConnOpenSet endU endV X (endV e₀) (B k₀)) :
-- imply
  ¬ psr_FamilyFrontierConn σf f endU endV B := by
-- proof
  apply StatMech.OSSS.FrontierFamilyClose.frf_familyFrontierConn_false σf f endU endV B k₀ he₀ X hnc hnotU hnotV

/--
[frf_familyFrontierConn_false_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FrontierFamilyClose.lean)
-/
@[path]
private lemma frf_familyFrontierConn_false_concrete_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {σf : κ → (Fin 3 ≃ Fin 3)}
  {k₀ : κ}
-- given
  (hk₀ : ((σf k₀).symm 0 : ℕ) = 0) :
-- imply
  ¬ psr_FamilyFrontierConn σf (indicatorConn psr_witnessEndU psr_witnessEndV ({0} : Set (Fin 4)) ({3} : Set (Fin 4))) psr_witnessEndU psr_witnessEndV (fun _ => ({0} : Set (Fin 4))) := by
-- proof
  apply StatMech.OSSS.FrontierFamilyClose.frf_familyFrontierConn_false_concrete σf k₀ hk₀

/--
[frf_mean_reveal_le_of_queried_imp_or](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FrontierFamilyClose.lean)
-/
@[path]
private lemma frf_mean_reveal_le_of_queried_imp_or_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {e : E}
  [DecidablePred P]
  [DecidablePred Q]
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (P Q : ConfigSpace E → Prop)
  (h : ∀ ω, e ∈ T.queried ω → P ω ∨ Q ω) :
-- imply
  revealmentMu μ T e ≤ Lindeberg.mean μ (fun ω => if P ω then (1 : ℝ) else 0) + Lindeberg.mean μ (fun ω => if Q ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.FrontierFamilyClose.frf_mean_reveal_le_of_queried_imp_or hμ0 T e P Q h

/--
[frf_mean_reveal_crossTree_le_connOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FrontierFamilyClose.lean)
-/
@[path]
private lemma frf_mean_reveal_crossTree_le_connOpen_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {μ : ConfigSpace E → ℝ}
  {endU endV : E → V}
  {o : V}
  {B C : Set V}
  {l : List E}
  {disc₀ : Finset V}
  {i : E}
  [DecidablePred (fun ω => ConnOpenSet endU endV ω (endU i) B)]
  [DecidablePred (fun ω => ConnOpenSet endU endV ω (endV i) B)]
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) :
-- imply
  revealmentMu μ (crossTree endU endV o C l disc₀) i ≤ Lindeberg.mean μ (fun ω => if ConnOpenSet endU endV ω (endU i) B then (1 : ℝ) else 0) + Lindeberg.mean μ (fun ω => if ConnOpenSet endU endV ω (endV i) B then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.FrontierFamilyClose.frf_mean_reveal_crossTree_le_connOpen hμ0 endU endV o B C l disc₀ hdisc₀ i

/--
[frf_mean_reveal_crossTree_le_connBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FrontierFamilyClose.lean)
-/
@[path]
private lemma frf_mean_reveal_crossTree_le_connBox_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {μ : ConfigSpace E → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {C : Set (Site d)}
  {k : ℕ}
  {l : List E}
  {disc₀ : Finset (Site d)}
  {i : E}
  [DecidablePred (fun ω => ConnOpenSet endU endV ω (endU i) (vertexBoundary d k))]
  [DecidablePred (fun ω => ConnOpenSet endU endV ω (endV i) (vertexBoundary d k))]
  [DecidablePred (fun ω => ConnectedToSet d (liftCfg edge ω) (endU i) (vertexBoundary d k))]
  [DecidablePred (fun ω => ConnectedToSet d (liftCfg edge ω) (endV i) (vertexBoundary d k))]
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ vertexBoundary d k) :
-- imply
  revealmentMu μ (crossTree endU endV o C l disc₀) i ≤ Lindeberg.mean μ (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU i) (vertexBoundary d k) then (1 : ℝ) else 0) + Lindeberg.mean μ (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV i) (vertexBoundary d k) then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.FrontierFamilyClose.frf_mean_reveal_crossTree_le_connBox hμ0 hinj hcoh hadj o C k l disc₀ hdisc₀ i

/--
[frf_var_le_avg_treeReveal_mul_sum_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FrontierFamilyClose.lean)
-/
@[path]
private lemma frf_var_le_avg_treeReveal_mul_sum_cov_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
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
  (hStep : ∀ k, StepCovBound μ (Tf k) f)
  (hD : ∀ e, (1 / (Fintype.card κ : ℝ)) * ∑ k, revealmentMu μ (Tf k) e ≤ D) :
-- imply
  Lindeberg.var μ f ≤ D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.FrontierFamilyClose.frf_var_le_avg_treeReveal_mul_sum_cov hpos hμ1 hFKG Tf hf hTf hStep D hD

/--
[frf_avg_treeReveal_le_of_perScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FrontierFamilyClose.lean)
-/
@[path]
private lemma frf_avg_treeReveal_le_of_perScale_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {μ : ConfigSpace E → ℝ}
  [Fintype κ]
  [Nonempty κ]
  {Tf : κ → DecisionTree E}
  {R : κ → E → ℝ}
  {D : ℝ}
-- given
  (hreach : ∀ k e, revealmentMu μ (Tf k) e ≤ R k e)
  (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
-- imply
  ∀ e, (1 / (Fintype.card κ : ℝ)) * ∑ k, revealmentMu μ (Tf k) e ≤ D := by
-- proof
  apply StatMech.OSSS.FrontierFamilyClose.frf_avg_treeReveal_le_of_perScale Tf R D hreach hsum

/--
[frf_fk_q2_cov_lower_bound_of_adaptiveFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FrontierFamilyClose.lean)
-/
@[path]
private lemma frf_fk_q2_cov_lower_bound_of_adaptiveFamily_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
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
  (hStep : ∀ k, StepCovBound (fkMass G p 2) (Tf k) f)
  (hDpos : 0 < D)
  (hreach : ∀ k e, revealmentMu (fkMass G p 2) (Tf k) e ≤ R k e)
  (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
-- imply
  Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f) / D ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.FrontierFamilyClose.frf_fk_q2_cov_lower_bound_of_adaptiveFamily G hp hp1 Tf hf hidem hTf hStep R D hDpos hreach hsum

/--
[frf_revealmentMu_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FrontierFamilyClose.lean)
-/
@[path]
private lemma frf_revealmentMu_le_one_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {e : E}
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  revealmentMu μ T e ≤ 1 := by
-- proof
  apply StatMech.OSSS.FrontierFamilyClose.frf_revealmentMu_le_one hμ0 hμ1 T e

/--
[frf_avg_treeReveal_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FrontierFamilyClose.lean)
-/
@[path]
private lemma frf_avg_treeReveal_le_one_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {μ : ConfigSpace E → ℝ}
  [Fintype κ]
  [Nonempty κ]
  {Tf : κ → DecisionTree E}
  {e : E}
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  (1 / (Fintype.card κ : ℝ)) * ∑ k, revealmentMu μ (Tf k) e ≤ 1 := by
-- proof
  apply StatMech.OSSS.FrontierFamilyClose.frf_avg_treeReveal_le_one hμ0 hμ1 Tf e

/--
[frf_fk_q2_cov_lower_bound_adaptive_poincare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FrontierFamilyClose.lean)
-/
@[path]
private lemma frf_fk_q2_cov_lower_bound_adaptive_poincare_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {p : ℝ}
  [Fintype κ]
  [Nonempty κ]
  {Tf : κ → DecisionTree (Sym2 W)}
  {f : ConfigSpace (Sym2 W) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hf : Monotone f)
  (hTf : ∀ k, (Tf k).evalR = f)
  (hStep : ∀ k, StepCovBound (fkMass G p 2) (Tf k) f) :
-- imply
  Lindeberg.var (fkMass G p 2) f ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.FrontierFamilyClose.frf_fk_q2_cov_lower_bound_adaptive_poincare G hp hp1 Tf hf hTf hStep


-- created on 2026-10-23
