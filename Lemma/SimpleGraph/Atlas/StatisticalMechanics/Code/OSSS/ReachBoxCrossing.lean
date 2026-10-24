import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.ReachBoxCrossing
open MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.ReachBoxCrossing


/--
[mean_indicator_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachBoxCrossing.lean)
-/
@[path]
private lemma mean_indicator_le_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {g : ConfigSpace E → ℝ}
  [DecidablePred P]
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (P : ConfigSpace E → Prop)
  (hg : ∀ X, g X ≤ if P X then (1 : ℝ) else 0) :
-- imply
  Lindeberg.mean μ g ≤ Lindeberg.mean μ (fun X => if P X then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.ReachBoxCrossing.mean_indicator_le hμ0 g P hg

/--
[reachProb_le_of_undet_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachBoxCrossing.lean)
-/
@[path]
private lemma reachProb_le_of_undet_imp_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  [DecidablePred P]
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (P : ConfigSpace E → Prop)
  (h : ∀ X, ¬ detAtC (σ : Fin n → E) f X (σ.symm e : ℕ) → P X) :
-- imply
  reachProb μ σ f e ≤ Lindeberg.mean μ (fun X => if P X then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.ReachBoxCrossing.reachProb_le_of_undet_imp hμ0 σ f e P h

/--
[mean_indicator_or_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachBoxCrossing.lean)
-/
@[path]
private lemma mean_indicator_or_le_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  [DecidablePred P]
  [DecidablePred Q]
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (P Q : ConfigSpace E → Prop) :
-- imply
  Lindeberg.mean μ (fun X => if P X ∨ Q X then (1 : ℝ) else 0) ≤ Lindeberg.mean μ (fun X => if P X then (1 : ℝ) else 0) + Lindeberg.mean μ (fun X => if Q X then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.ReachBoxCrossing.mean_indicator_or_le hμ0 P Q

/--
[reachProb_le_of_undet_imp_or](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachBoxCrossing.lean)
-/
@[path]
private lemma reachProb_le_of_undet_imp_or_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {e : E}
  [DecidablePred P]
  [DecidablePred Q]
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (P Q : ConfigSpace E → Prop)
  (h : ∀ X, ¬ detAtC (σ : Fin n → E) f X (σ.symm e : ℕ) → P X ∨ Q X) :
-- imply
  reachProb μ σ f e ≤ Lindeberg.mean μ (fun X => if P X then (1 : ℝ) else 0) + Lindeberg.mean μ (fun X => if Q X then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.ReachBoxCrossing.reachProb_le_of_undet_imp_or hμ0 σ f e P Q h

/--
[reachProb_le_connOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachBoxCrossing.lean)
-/
@[path]
private lemma reachProb_le_connOpen_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {endU endV : E → V}
  {B : Set V}
  {e : E}
  [DecidablePred (fun X => ConnOpenSet endU endV X (endU e) B)]
  [DecidablePred (fun X => ConnOpenSet endU endV X (endV e) B)]
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (hfront : FrontierConn σ f endU endV B e) :
-- imply
  reachProb μ σ f e ≤ Lindeberg.mean μ (fun X => if ConnOpenSet endU endV X (endU e) B then (1 : ℝ) else 0) + Lindeberg.mean μ (fun X => if ConnOpenSet endU endV X (endV e) B then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.ReachBoxCrossing.reachProb_le_connOpen hμ0 σ f endU endV B e hfront

/--
[mean_indicator_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachBoxCrossing.lean)
-/
@[path]
private lemma mean_indicator_mono_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {μ : ConfigSpace E → ℝ}
  [DecidablePred P]
  [DecidablePred Q]
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (P Q : ConfigSpace E → Prop)
  (h : ∀ X, P X → Q X) :
-- imply
  Lindeberg.mean μ (fun X => if P X then (1 : ℝ) else 0) ≤ Lindeberg.mean μ (fun X => if Q X then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.ReachBoxCrossing.mean_indicator_mono hμ0 P Q h

/--
[reachProb_le_connBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachBoxCrossing.lean)
-/
@[path]
private lemma reachProb_le_connBox_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {k : ℕ}
  {e : E}
  [DecidablePred (fun X => ConnOpenSet endU endV X (endU e) (vertexBoundary d k))]
  [DecidablePred (fun X => ConnOpenSet endU endV X (endV e) (vertexBoundary d k))]
  [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k))]
  [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k))]
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hfront : FrontierConn σ f endU endV (vertexBoundary d k) e) :
-- imply
  reachProb μ σ f e ≤ Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) + Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.ReachBoxCrossing.reachProb_le_connBox hμ0 σ f hinj hcoh hadj k e hfront

/--
[revealAdapt_le_connBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachBoxCrossing.lean)
-/
@[path]
private lemma revealAdapt_le_connBox_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {k : ℕ}
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
  (hfront : FrontierConn σ f endU endV (vertexBoundary d k) e) :
-- imply
  revealAdapt μ σ f e ≤ Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) + Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.ReachBoxCrossing.revealAdapt_le_connBox hpos hμ1 σ f hinj hcoh hadj k e hfront

/--
[os_cov_lower_bound_from_box_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachBoxCrossing.lean)
-/
@[path]
private lemma os_cov_lower_bound_from_box_crossing_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {k : ℕ}
  {D : ℝ}
  [∀ e X, Decidable (ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k))]
  [∀ e X, Decidable (ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k))]
  [∀ e X, Decidable (ConnOpenSet endU endV X (endU e) (vertexBoundary d k))]
  [∀ e X, Decidable (ConnOpenSet endU endV X (endV e) (vertexBoundary d k))]
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1)
  (hidem : ∀ ω, f ω * f ω = f ω)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hDpos : 0 < D)
  (hfront : ∀ e, FrontierConn σ f endU endV (vertexBoundary d k) e)
  (hbox : ∀ e, Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) + Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ D) :
-- imply
  Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) / D ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.ReachBoxCrossing.os_cov_lower_bound_from_box_crossing hpos hμ1 hFKG hmono σ hf hf0 hf1 hidem hinj hcoh hadj k D hDpos hfront hbox

/--
[frontierConn_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachBoxCrossing.lean)
-/
@[path]
private lemma frontierConn_univ_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  [DecidableEq V]
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {endU endV : E → V}
  {e : E} :
-- imply
  FrontierConn σ f endU endV (Set.univ : Set V) e := by
-- proof
  apply StatMech.OSSS.ReachBoxCrossing.frontierConn_univ σ f endU endV e

/--
[frontierConn_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ReachBoxCrossing.lean)
-/
@[path]
private lemma frontierConn_satisfiable_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  [DecidableEq V]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
  {endU endV : E → V}
  {e : E}
  [DecidablePred (fun X => ConnOpenSet endU endV X (endU e) (Set.univ : Set V))]
  [DecidablePred (fun X => ConnOpenSet endU endV X (endV e) (Set.univ : Set V))]
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω) :
-- imply
  reachProb μ σ f e ≤ Lindeberg.mean μ (fun X => if ConnOpenSet endU endV X (endU e) (Set.univ : Set V) then (1 : ℝ) else 0) + Lindeberg.mean μ (fun X => if ConnOpenSet endU endV X (endV e) (Set.univ : Set V) then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.ReachBoxCrossing.frontierConn_satisfiable hμ0 σ f endU endV e


-- created on 2026-10-23
