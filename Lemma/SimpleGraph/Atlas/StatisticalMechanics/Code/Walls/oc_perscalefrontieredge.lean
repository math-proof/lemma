import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc_perscalefrontieredge
open MeasureTheory StatMech StatMech.Walls


/--
[oc_perscale_frontier_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_perscalefrontieredge.lean)
-/
@[path]
private lemma oc_perscale_frontier_edge_eq
  [Fintype E]
  [DecidableEq E]
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
  apply StatMech.Walls.oc_perscale_frontier_edge hpos hμ1 hinj hcoh hadj k n nE hnE hne

/--
[oc_perscale_frontier_edge_high_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_perscalefrontieredge.lean)
-/
@[path]
private lemma oc_perscale_frontier_edge_high_pos_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {μ : ConfigSpace E → ℝ}
  {nE : ℕ}
  {σ : Fin nE ≃ E}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {k n : ℕ}
  {e : E}
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
  apply StatMech.Walls.oc_perscale_frontier_edge_high_pos hpos hμ1 σ hinj hcoh hadj k n hσ e he

/--
[oc_topIncident_of_endU_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_perscalefrontieredge.lean)
-/
@[path]
private lemma oc_topIncident_of_endU_mem_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {B : Set V}
  {e₀ : E}
-- given
  (hmem : endU e₀ ∈ B) :
-- imply
  TopIncident endU endV B e₀ := by
-- proof
  apply StatMech.Walls.oc_topIncident_of_endU_mem hmem

/--
[oc_frontier_edge_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_perscalefrontieredge.lean)
-/
@[path]
private lemma oc_frontier_edge_nonvacuous_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {B : Set V}
  {e₀ : E}
-- given
  (hmem : endU e₀ ∈ B) :
-- imply
  (Finset.univ.filter (TopIncident endU endV B)).Nonempty := by
-- proof
  apply StatMech.Walls.oc_frontier_edge_nonvacuous hmem


-- created on 2026-10-23
