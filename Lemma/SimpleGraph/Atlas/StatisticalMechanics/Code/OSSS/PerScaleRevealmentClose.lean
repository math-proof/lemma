import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.PerScaleRevealmentClose.Part3
open MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.PerScaleRevealmentClose


/--
[psr_frontierConn_first_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PerScaleRevealmentClose.lean)
-/
@[path]
private lemma psr_frontierConn_first_iff_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {endU endV : E → V}
  {B : Set V}
  {e₀ : E}
-- given
  (he₀ : (σ.symm e₀ : ℕ) = 0) :
-- imply
  FrontierConn σ f endU endV B e₀ ↔ ∀ X : ConfigSpace E, (∃ w, f w ≠ f X) → ConnOpenSet endU endV X (endU e₀) B ∨ ConnOpenSet endU endV X (endV e₀) B := by
-- proof
  apply StatMech.OSSS.PerScaleRevealmentClose.psr_frontierConn_first_iff σ f endU endV B he₀

/--
[psr_frontierConn_first_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PerScaleRevealmentClose.lean)
-/
@[path]
private lemma psr_frontierConn_first_refutable_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {endU endV : E → V}
  {B : Set V}
  {e₀ : E}
  {X : ConfigSpace E}
-- given
  (he₀ : (σ.symm e₀ : ℕ) = 0)
  (hnc : ∃ w, f w ≠ f X)
  (hnotU : ¬ ConnOpenSet endU endV X (endU e₀) B)
  (hnotV : ¬ ConnOpenSet endU endV X (endV e₀) B) :
-- imply
  ¬ FrontierConn σ f endU endV B e₀ := by
-- proof
  apply StatMech.OSSS.PerScaleRevealmentClose.psr_frontierConn_first_refutable σ f endU endV B he₀ X hnc hnotU hnotV

/--
[psr_revealAdapt_first_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PerScaleRevealmentClose.lean)
-/
@[path]
private lemma psr_revealAdapt_first_gt_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e₀ : E}
  {c : ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (he₀ : (σ.symm e₀ : ℕ) = 0)
  (hnc : ∀ X, ¬ ∀ w, f w = f X)
  (hc : c < 1) :
-- imply
  ¬ revealAdapt μ σ f e₀ ≤ c := by
-- proof
  apply StatMech.OSSS.PerScaleRevealmentClose.psr_revealAdapt_first_gt hpos hμ1 σ f he₀ hnc hc

/--
[psr_frontierConn_first_refutable_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PerScaleRevealmentClose.lean)
-/
@[path]
private lemma psr_frontierConn_first_refutable_witness_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {endU endV : E → V}
  {B C : Set V}
  {e₀ : E}
  {X w : ConfigSpace E}
-- given
  (he₀ : (σ.symm e₀ : ℕ) = 0)
  (hX0 : ¬ ∃ x ∈ C, ConnOpenSet endU endV X x B)
  (hw1 : ∃ x ∈ C, ConnOpenSet endU endV w x B)
  (hnotU : ¬ ConnOpenSet endU endV X (endU e₀) B)
  (hnotV : ¬ ConnOpenSet endU endV X (endV e₀) B) :
-- imply
  ¬ FrontierConn σ (indicatorConn endU endV B C) endU endV B e₀ := by
-- proof
  apply StatMech.OSSS.PerScaleRevealmentClose.psr_frontierConn_first_refutable_witness σ endU endV B C he₀ X w hX0 hw1 hnotU hnotV

/--
[psr_revealAdapt_le_connBox_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PerScaleRevealmentClose.lean)
-/
@[path]
private lemma psr_revealAdapt_le_connBox_of_pos_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {μ : ConfigSpace E → ℝ}
  {nE : ℕ}
  {σ : Fin nE ≃ E}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {k n : ℕ}
  {e : E}
  [DecidablePred (fun X => ConnOpenSet endU endV X (endU e) (vertexBoundary d k))]
  [DecidablePred (fun X => ConnOpenSet endU endV X (endV e) (vertexBoundary d k))]
  [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k))]
  [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k))]
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hσ : ∀ e' : E, (TopIncident endU endV (vertexBoundary d k) e' ↔ (σ.symm e' : ℕ) < (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).card))
  (he : (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).card - 1 ≤ (σ.symm e : ℕ)) :
-- imply
  revealAdapt μ σ (indicatorConn endU endV (vertexBoundary d k) (vertexBoundary d n)) e ≤ Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) + Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.PerScaleRevealmentClose.psr_revealAdapt_le_connBox_of_pos hpos hμ1 σ hinj hcoh hadj k n hσ e he

/--
[psr_revealAdapt_le_connBox_frontier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PerScaleRevealmentClose.lean)
-/
@[path]
private lemma psr_revealAdapt_le_connBox_frontier_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {μ : ConfigSpace E → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {k n : ℕ}
  {nE : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hnE : Fintype.card E = nE)
  (hne : (Finset.univ.filter (TopIncident endU endV (vertexBoundary d k))).Nonempty) :
-- imply
  ∃ (σ : Fin nE ≃ E) (e : E), TopIncident endU endV (vertexBoundary d k) e ∧ revealAdapt μ σ (indicatorConn endU endV (vertexBoundary d k) (vertexBoundary d n)) e ≤ Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) + Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.PerScaleRevealmentClose.psr_revealAdapt_le_connBox_frontier hpos hμ1 hinj hcoh hadj k n nE hnE hne

/--
[psr_perScale_of_familyFrontierConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PerScaleRevealmentClose.lean)
-/
@[path]
private lemma psr_perScale_of_familyFrontierConn_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {μ : ConfigSpace E → ℝ}
  {nE : ℕ}
  {σf : κ → (Fin nE ≃ E)}
  {f : ConfigSpace E → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {kscale : κ → ℕ}
  [∀ k e X, Decidable (ConnOpenSet endU endV X (endU e) (vertexBoundary d (kscale k)))]
  [∀ k e X, Decidable (ConnOpenSet endU endV X (endV e) (vertexBoundary d (kscale k)))]
  [∀ k e X, Decidable (ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d (kscale k)))]
  [∀ k e X, Decidable (ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d (kscale k)))]
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hfront : psr_FamilyFrontierConn σf f endU endV (fun k => vertexBoundary d (kscale k))) :
-- imply
  ∀ (k : κ) (e : E), revealAdapt μ (σf k) f e ≤ Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d (kscale k)) then (1 : ℝ) else 0) + Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d (kscale k)) then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.PerScaleRevealmentClose.psr_perScale_of_familyFrontierConn hpos hμ1 σf f hinj hcoh hadj kscale hfront

/--
[psr_fk_q2_cov_lower_bound_of_perScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PerScaleRevealmentClose.lean)
-/
@[path]
private lemma psr_fk_q2_cov_lower_bound_of_perScale_eq
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
  {nE : ℕ}
  {σf : κ → (Fin nE ≃ Sym2 W)}
  {f : ConfigSpace (Sym2 W) → ℝ}
  {R : κ → Sym2 W → ℝ}
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
  apply StatMech.OSSS.PerScaleRevealmentClose.psr_fk_q2_cov_lower_bound_of_perScale G hp hp1 σf hf hf0 hf1 hidem R D hDpos hreach hsum

/--
[psr_familyFrontierConn_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PerScaleRevealmentClose.lean)
-/
@[path]
private lemma psr_familyFrontierConn_univ_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {nE : ℕ}
  {σf : κ → (Fin nE ≃ E)}
  {f : ConfigSpace E → ℝ}
  {endU endV : E → V} :
-- imply
  psr_FamilyFrontierConn σf f endU endV (fun _ => (Set.univ : Set V)) := by
-- proof
  apply StatMech.OSSS.PerScaleRevealmentClose.psr_familyFrontierConn_univ σf f endU endV

/--
[psr_reachOpen_allClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PerScaleRevealmentClose.lean)
-/
@[path]
private lemma psr_reachOpen_allClosed_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {x y : V}
-- given
  (h : ReachOpen endU endV (fun _ => false) x y) :
-- imply
  x = y := by
-- proof
  apply StatMech.OSSS.PerScaleRevealmentClose.psr_reachOpen_allClosed h

/--
[psr_frontierConn_first_false_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PerScaleRevealmentClose.lean)
-/
@[path]
private lemma psr_frontierConn_first_false_concrete_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {σ : Fin 3 ≃ Fin 3}
-- given
  (he₀ : (σ.symm 0 : ℕ) = 0) :
-- imply
  ¬ FrontierConn σ (indicatorConn psr_witnessEndU psr_witnessEndV ({0} : Set (Fin 4)) ({3} : Set (Fin 4))) psr_witnessEndU psr_witnessEndV ({0} : Set (Fin 4)) (0 : Fin 3) := by
-- proof
  apply StatMech.OSSS.PerScaleRevealmentClose.psr_frontierConn_first_false_concrete σ he₀


-- created on 2026-10-23
