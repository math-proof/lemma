import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.QueriedCrossTreeClose
open MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.QueriedCrossTreeClose


/--
[incidentCluster_of_queried_crossTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/QueriedCrossTreeClose.lean)
-/
@[path]
private lemma incidentCluster_of_queried_crossTree_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {B C : Set V}
  {l : List E}
  {disc₀ : Finset V}
  {ω : ConfigSpace E}
  {i : E}
-- given
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
  (hi : i ∈ (crossTree endU endV o C l disc₀).queried ω) :
-- imply
  IncidentCluster endU endV ω B i := by
-- proof
  apply StatMech.OSSS.QueriedCrossTreeClose.incidentCluster_of_queried_crossTree endU endV o B C l disc₀ hdisc₀ ω i hi

/--
[reveal_crossTree_le_incidentCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/QueriedCrossTreeClose.lean)
-/
@[path]
private lemma reveal_crossTree_le_incidentCluster_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {ν : E → Bool → ℝ}
  {endU endV : E → V}
  {o : V}
  {B C : Set V}
  {l : List E}
  {disc₀ : Finset V}
  {i : E}
-- given
  (hν : IsProbWeight ν)
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) :
-- imply
  reveal ν (crossTree endU endV o C l disc₀) i ≤ expect ν (fun ω => if ConnOpenSet endU endV ω (endU i) B then (1 : ℝ) else 0) + expect ν (fun ω => if ConnOpenSet endU endV ω (endV i) B then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.QueriedCrossTreeClose.reveal_crossTree_le_incidentCluster hν endU endV o B C l disc₀ hdisc₀ i

/--
[reveal_crossTree_le_connBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/QueriedCrossTreeClose.lean)
-/
@[path]
private lemma reveal_crossTree_le_connBox_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {ν : E → Bool → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {C : Set (Site d)}
  {k : ℕ}
  {l : List E}
  {disc₀ : Finset (Site d)}
  {i : E}
-- given
  (hν : IsProbWeight ν)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ vertexBoundary d k) :
-- imply
  reveal ν (crossTree endU endV o C l disc₀) i ≤ expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU i) (vertexBoundary d k) then (1 : ℝ) else 0) + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV i) (vertexBoundary d k) then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.QueriedCrossTreeClose.reveal_crossTree_le_connBox hν hinj hcoh hadj o C k l disc₀ hdisc₀ i

/--
[covSum_ge_crossTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/QueriedCrossTreeClose.lean)
-/
@[path]
private lemma covSum_ge_crossTree_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {n : ℕ}
  {ν : E → Bool → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {l : List E}
  {disc₀ : ℕ → Finset (Site d)}
  {c₀ : ℝ}
  {D : ℝ}
-- given
  (hn : 1 ≤ n)
  (hν : IsProbWeight ν)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
  (hl : ∀ e, e ∈ l)
  (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
  (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
  (hoB : ∀ k, o ∉ disc₀ k)
  (hc₀nn : 0 ≤ c₀)
  (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
  (hDnn : 0 ≤ D)
  (hD : ∀ e, (∑ k ∈ Finset.Icc 1 n, (expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0) + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0))) ≤ D) :
-- imply
  (n : ℝ) * c₀ * (expect ν ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) * (1 - expect ν ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))))) ≤ D * ∑ e, cov ν (coordI e) ((crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.OSSS.QueriedCrossTreeClose.covSum_ge_crossTree hn hν hinj hcoh hadj o ho l hl disc₀ hdisc₀sub hdisc₀sup hoB c₀ hc₀nn hc₀ D hDnn hD


-- created on 2026-10-23
