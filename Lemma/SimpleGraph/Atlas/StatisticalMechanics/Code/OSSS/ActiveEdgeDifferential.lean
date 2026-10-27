import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.ActiveEdgeDifferential.Part2
open Finset Set StatMech StatMech.OSSS StatMech.OSSS.ActiveEdgeDifferential


/--
[mean_active_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ActiveEdgeDifferential.lean)
-/
@[path]
private lemma mean_active_eq_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {f : ConfigSpace G.edgeSet → ℝ} :
-- imply
  Lindeberg.mean (FK.activeProb G pf q) f = FK.activeMean G pf q f := by
-- proof
  apply StatMech.OSSS.ActiveEdgeDifferential.mean_active_eq G pf q f

/--
[cov_active_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ActiveEdgeDifferential.lean)
-/
@[path]
private lemma cov_active_eq_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {f g : ConfigSpace G.edgeSet → ℝ} :
-- imply
  Lindeberg.cov (FK.activeProb G pf q) f g = FK.activeCov G pf q f g := by
-- proof
  apply StatMech.OSSS.ActiveEdgeDifferential.cov_active_eq G pf q f g

/--
[reachOpen_first_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ActiveEdgeDifferential.lean)
-/
@[path]
private lemma reachOpen_first_incident_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {endU endV : E → X}
  {ω : ConfigSpace E}
  {x z : X}
-- given
  (h : ReachOpen endU endV ω x z)
  (hne : x ≠ z) :
-- imply
  ∃ e, ω e = true ∧ (endU e = x ∨ endV e = x) := by
-- proof
  apply StatMech.OSSS.ActiveEdgeDifferential.reachOpen_first_incident h hne

/--
[closedProd_incident_le_cross_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ActiveEdgeDifferential.lean)
-/
@[path]
private lemma closedProd_incident_le_cross_complement_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  [Fintype E]
  [DecidableEq E]
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {B : Set (Site d)}
  {ω : ConfigSpace E}
-- given
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hoB : o ∉ B) :
-- imply
  FK.closedProd (incidentEdges endU endV o) ω ≤ 1 - (crossEvent edge o B).indicator (fun _ => (1 : ℝ)) ω := by
-- proof
  apply StatMech.OSSS.ActiveEdgeDifferential.closedProd_incident_le_cross_complement hcoh o B hoB ω

/--
[active_cross_one_sub_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ActiveEdgeDifferential.lean)
-/
@[path]
private lemma active_cross_one_sub_lower_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {q β β₀ : ℝ}
  {edge : G.edgeSet → Sym2 (Site d)}
  {endU endV : G.edgeSet → Site d}
  {o : Site d}
  {B : Set (Site d)}
-- given
  (hJ : ∀ e, 0 < J e)
  (hq : 1 ≤ q)
  (hβ : 0 < β)
  (hββ₀ : β ≤ β₀)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hoB : o ∉ B) :
-- imply
  (∏ e ∈ incidentEdges endU endV o, Real.exp (-(β₀ * J e.1))) ≤ 1 - Lindeberg.mean (FK.activeProb G (FK.betaParams J β) q) ((crossEvent edge o B).indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.OSSS.ActiveEdgeDifferential.active_cross_one_sub_lower G J hJ q β β₀ hq hβ hββ₀ hcoh o B hoB

/--
[active_fk_differential_logistic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ActiveEdgeDifferential.lean)
-/
@[path]
private lemma active_fk_differential_logistic_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Nonempty G.edgeSet]
  {J : Sym2 V → ℝ}
  {q β : ℝ}
  {edge : G.edgeSet → Sym2 (Site d)}
  {endU endV : G.edgeSet → Site d}
  {o : Site d}
  {l : List G.edgeSet}
  {disc₀ : ℕ → Finset (Site d)}
  {n : ℕ}
  {Λ : Finset (Site d)}
-- given
  (hJ : ∀ e, 0 < J e)
  (hq : 1 ≤ q)
  (hβ : 0 < β)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hl : ∀ e, e ∈ l)
  (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
  (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
  (hoB : ∀ k, o ∉ disc₀ k)
  (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
  (hn : 1 ≤ n)
  (hne : Λ.Nonempty)
  (hLu : ∀ e : G.edgeSet, endU e ∈ Λ)
  (hLv : ∀ e : G.edgeSet, endV e ∈ Λ)
  (hUbox : ∀ e : G.edgeSet, endU e ∈ box d n)
  (hVbox : ∀ e : G.edgeSet, endV e ∈ box d n) :
-- imply
  ∃ cR : ℝ, 0 < cR ∧ cR * (Lindeberg.mean (FK.activeProb G (FK.betaParams J β) q) (crossIndG edge o n) * (1 - Lindeberg.mean (FK.activeProb G (FK.betaParams J β) q) (crossIndG edge o n)) / (4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n, Lindeberg.mean (FK.activeProb G (FK.betaParams J β) q) (fun ω => if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x j) then (1 : ℝ) else 0)) / (n : ℝ))) ≤ deriv (fun b => FK.activeProbOf G (FK.betaParams J b) q (crossEvent edge o (vertexBoundary d n))) β := by
-- proof
  apply StatMech.OSSS.ActiveEdgeDifferential.active_fk_differential_logistic G J hJ q β hq hβ hinj hcoh hadj o l hl disc₀ hdisc₀sub hdisc₀sup hoB ho n hn Λ hne hLu hLv hUbox hVbox

/--
[geometricDenom_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ActiveEdgeDifferential.lean)
-/
@[path]
private lemma geometricDenom_pos_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {edge : E → Sym2 (Site d)}
  {n : ℕ}
  {Λ : Finset (Site d)}
-- given
  (hμ0 : ∀ ω, 0 ≤ μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hn : 1 ≤ n)
  (hne : Λ.Nonempty) :
-- imply
  0 < 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n, Lindeberg.mean μ (fun ω => if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x j) then (1 : ℝ) else 0)) / (n : ℝ) := by
-- proof
  apply StatMech.OSSS.ActiveEdgeDifferential.geometricDenom_pos μ hμ0 hμ1 edge n hn Λ hne

/--
[absorb_cross_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ActiveEdgeDifferential.lean)
-/
@[path]
private lemma absorb_cross_complement_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {θ D κ cR θ' : ℝ}
-- given
  (hθ : 0 ≤ θ)
  (hD : 0 < D)
  (hκ : 0 < κ)
  (hcR : 0 < cR)
  (hgap : κ ≤ 1 - θ)
  (hlog : cR * (θ * (1 - θ) / D) ≤ θ') :
-- imply
  0 < cR * κ ∧ (cR * κ) * (θ / D) ≤ θ' := by
-- proof
  apply StatMech.OSSS.ActiveEdgeDifferential.absorb_cross_complement hθ hD hκ hcR hgap hlog

/--
[active_fk_differential_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ActiveEdgeDifferential.lean)
-/
@[path]
private lemma active_fk_differential_inequality_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Nonempty G.edgeSet]
  {J : Sym2 V → ℝ}
  {q β β₀ : ℝ}
  {edge : G.edgeSet → Sym2 (Site d)}
  {endU endV : G.edgeSet → Site d}
  {o : Site d}
  {l : List G.edgeSet}
  {disc₀ : ℕ → Finset (Site d)}
  {n : ℕ}
  {Λ : Finset (Site d)}
-- given
  (hJ : ∀ e, 0 < J e)
  (hq : 1 ≤ q)
  (hβ : 0 < β)
  (hββ₀ : β ≤ β₀)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hl : ∀ e, e ∈ l)
  (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
  (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
  (hoB : ∀ k, o ∉ disc₀ k)
  (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
  (hn : 1 ≤ n)
  (hne : Λ.Nonempty)
  (hLu : ∀ e : G.edgeSet, endU e ∈ Λ)
  (hLv : ∀ e : G.edgeSet, endV e ∈ Λ)
  (hUbox : ∀ e : G.edgeSet, endU e ∈ box d n)
  (hVbox : ∀ e : G.edgeSet, endV e ∈ box d n) :
-- imply
  ∃ c : ℝ, 0 < c ∧ c * (Lindeberg.mean (FK.activeProb G (FK.betaParams J β) q) (crossIndG edge o n) / (4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n, Lindeberg.mean (FK.activeProb G (FK.betaParams J β) q) (fun ω => if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x j) then (1 : ℝ) else 0)) / (n : ℝ))) ≤ deriv (fun b => FK.activeProbOf G (FK.betaParams J b) q (crossEvent edge o (vertexBoundary d n))) β := by
-- proof
  apply StatMech.OSSS.ActiveEdgeDifferential.active_fk_differential_inequality G J hJ q β β₀ hq hβ hββ₀ hinj hcoh hadj o l hl disc₀ hdisc₀sub hdisc₀sup hoB ho n hn Λ hne hLu hLv hUbox hVbox


-- created on 2026-10-23
