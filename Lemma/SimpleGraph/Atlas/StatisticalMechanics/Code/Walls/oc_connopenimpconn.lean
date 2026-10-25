import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc_connopenimpconn.Part2
open StatMech StatMech.Walls


/--
[oc_reachOpen_imp_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_connopenimpconn.lean)
-/
@[path]
private lemma oc_reachOpen_imp_connected_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {ω : ConfigSpace E}
  {x y : Site d}
-- given
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (h : ReachOpen endU endV ω x y) :
-- imply
  Connected d (liftCfg edge ω) x y := by
-- proof
  apply StatMech.Walls.oc_reachOpen_imp_connected hinj hcoh hadj h

/--
[oc_connOpenSet_imp_connectedToSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_connopenimpconn.lean)
-/
@[path]
private lemma oc_connOpenSet_imp_connectedToSet_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {ω : ConfigSpace E}
  {x : Site d}
  {B : Set (Site d)}
-- given
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (h : ConnOpenSet endU endV ω x B) :
-- imply
  ConnectedToSet d (liftCfg edge ω) x B := by
-- proof
  apply StatMech.Walls.oc_connOpenSet_imp_connectedToSet hinj hcoh hadj h

/--
[oc_mean_connOpen_le_connBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_connopenimpconn.lean)
-/
@[path]
private lemma oc_mean_connOpen_le_connBox_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {μ : ConfigSpace E → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {k : ℕ}
  {x : Site d}
  [DecidablePred (fun X => ConnOpenSet endU endV X x (vertexBoundary d k))]
  [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) x (vertexBoundary d k))]
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e)) :
-- imply
  Lindeberg.mean μ (fun X => if ConnOpenSet endU endV X x (vertexBoundary d k) then (1 : ℝ) else 0) ≤ Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) x (vertexBoundary d k) then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Walls.oc_mean_connOpen_le_connBox hμ0 hinj hcoh hadj k x

/--
[oc_mean_connOpen_sum_le_connBox_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_connopenimpconn.lean)
-/
@[path]
private lemma oc_mean_connOpen_sum_le_connBox_sum_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {μ : ConfigSpace E → ℝ}
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
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e)) :
-- imply
  Lindeberg.mean μ (fun X => if ConnOpenSet endU endV X (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) + Lindeberg.mean μ (fun X => if ConnOpenSet endU endV X (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) ≤ Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) + Lindeberg.mean μ (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Walls.oc_mean_connOpen_sum_le_connBox_sum hμ0 hinj hcoh hadj k e

/--
[oc_reachProb_le_connBox_via_conversion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_connopenimpconn.lean)
-/
@[path]
private lemma oc_reachProb_le_connBox_via_conversion_eq
  [Fintype E]
  [DecidableEq E]
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
  apply StatMech.Walls.oc_reachProb_le_connBox_via_conversion hμ0 σ f hinj hcoh hadj k e hfront

/--
[oc_adj_site0_site1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_connopenimpconn.lean)
-/
@[path]
private lemma oc_adj_site0_site1_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  (hypercubicLattice 1).Adj oc_site0 oc_site1 := by
-- proof
  apply StatMech.Walls.oc_adj_site0_site1

/--
[oc_witness_hcoh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_connopenimpconn.lean)
-/
@[path]
private lemma oc_witness_hcoh_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ∀ e, oc_witnessEdge e = s(oc_witnessEndU e, oc_witnessEndV e) := by
-- proof
  apply StatMech.Walls.oc_witness_hcoh

/--
[oc_witness_hadj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_connopenimpconn.lean)
-/
@[path]
private lemma oc_witness_hadj_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ∀ e, (hypercubicLattice 1).Adj (oc_witnessEndU e) (oc_witnessEndV e) := by
-- proof
  apply StatMech.Walls.oc_witness_hadj

/--
[oc_witness_hinj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_connopenimpconn.lean)
-/
@[path]
private lemma oc_witness_hinj_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  Function.Injective oc_witnessEdge := by
-- proof
  apply StatMech.Walls.oc_witness_hinj

/--
[oc_connectedToSet_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_connopenimpconn.lean)
-/
@[path]
private lemma oc_connectedToSet_witness_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ConnectedToSet 1 (liftCfg oc_witnessEdge (fun _ => true)) oc_site0 ({oc_site1} : Set (Site 1)) := by
-- proof
  apply StatMech.Walls.oc_connectedToSet_witness

/--
[oc_site0_ne_site1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_connopenimpconn.lean)
-/
@[path]
private lemma oc_site0_ne_site1_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  oc_site0 ≠ oc_site1 := by
-- proof
  apply StatMech.Walls.oc_site0_ne_site1


-- created on 2026-10-23
