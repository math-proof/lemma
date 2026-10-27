import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FiniteGraphBoundaryDifferential
open Finset Set StatMech StatMech.OSSS StatMech.OSSS.FiniteGraphBoundaryDifferential


/--
[openCrossEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FiniteGraphBoundaryDifferential.lean)
-/
@[path]
private lemma openCrossEvent_isIncreasing_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype E]
  [DecidableEq E]
  {endU endV : E → V}
  {o : V}
  {B : Set V} :
-- imply
  IsIncreasing (openCrossEvent endU endV o B) := by
-- proof
  apply StatMech.OSSS.FiniteGraphBoundaryDifferential.openCrossEvent_isIncreasing endU endV o B

/--
[closedProd_incident_le_openCross_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FiniteGraphBoundaryDifferential.lean)
-/
@[path]
private lemma closedProd_incident_le_openCross_complement_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype E]
  [DecidableEq E]
  {endU endV : E → V}
  {o : V}
  {B : Set V}
  {omega : ConfigSpace E}
-- given
  (hoB : o ∉ B) :
-- imply
  FK.closedProd (openIncidentEdges endU endV o) omega ≤ 1 - (openCrossEvent endU endV o B).indicator (fun _ => (1 : Real)) omega := by
-- proof
  apply StatMech.OSSS.FiniteGraphBoundaryDifferential.closedProd_incident_le_openCross_complement endU endV o B hoB omega

/--
[closedProd_reindexedIncident_le_openCross_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FiniteGraphBoundaryDifferential.lean)
-/
@[path]
private lemma closedProd_reindexedIncident_le_openCross_complement_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype E]
  [DecidableEq E]
  [Fintype I]
  [DecidableEq I]
  [Fintype O]
  [DecidableEq O]
  {iota : I → O}
  {endU endV : I → V}
  {o : V}
  {B : Set V}
  {omega : ConfigSpace O}
-- given
  (hoB : o ∉ B) :
-- imply
  FK.closedProd (reindexedOpenIncidentEdges iota endU endV o) omega ≤ 1 - (openCrossEvent endU endV o B).indicator (fun _ => (1 : Real)) (restrictConfig iota omega) := by
-- proof
  apply StatMech.OSSS.FiniteGraphBoundaryDifferential.closedProd_reindexedIncident_le_openCross_complement iota endU endV o B hoB omega

/--
[activeBC_reindexed_openCross_one_sub_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FiniteGraphBoundaryDifferential.lean)
-/
@[path]
private lemma activeBC_reindexed_openCross_one_sub_lower_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype E]
  [DecidableEq E]
  [Fintype I]
  [DecidableEq I]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {J : Sym2 V → Real}
  {q beta beta0 : Real}
  {iota : I → G.edgeSet}
  {endU endV : I → W}
  {o : W}
  {B : Set W}
-- given
  (hJ : ∀ e, 0 < J e)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hbeta0 : beta ≤ beta0)
  (hoB : o ∉ B) :
-- imply
  (reindexedOpenIncidentEdges iota endU endV o).prod (fun e => Real.exp (-(beta0 * J e.1))) ≤ 1 - Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q) (fun omega => (openCrossEvent endU endV o B).indicator (fun _ => (1 : Real)) (restrictConfig iota omega)) := by
-- proof
  apply StatMech.OSSS.FiniteGraphBoundaryDifferential.activeBC_reindexed_openCross_one_sub_lower G C J hJ q beta beta0 hq hbeta hbeta0 iota endU endV o B hoB

/--
[activeBC_openCross_one_sub_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FiniteGraphBoundaryDifferential.lean)
-/
@[path]
private lemma activeBC_openCross_one_sub_lower_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype E]
  [DecidableEq E]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {J : Sym2 V → Real}
  {q beta beta0 : Real}
  {endU endV : G.edgeSet → V}
  {o : V}
  {B : Set V}
-- given
  (hJ : ∀ e, 0 < J e)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hbeta0 : beta ≤ beta0)
  (hoB : o ∉ B) :
-- imply
  (openIncidentEdges endU endV o).prod (fun e => Real.exp (-(beta0 * J e.1))) ≤ 1 - Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q) ((openCrossEvent endU endV o B).indicator fun _ => (1 : Real)) := by
-- proof
  apply StatMech.OSSS.FiniteGraphBoundaryDifferential.activeBC_openCross_one_sub_lower G C J hJ q beta beta0 hq hbeta hbeta0 endU endV o B hoB

/--
[hcov_openCross_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FiniteGraphBoundaryDifferential.lean)
-/
@[path]
private lemma hcov_openCross_mass_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → Real}
  {endU endV : E → V}
  {o : V}
  {l : List E}
  {shell disc : Nat → Finset V}
  {n : Nat}
  {D : Real}
-- given
  (hpos : ∀ omega, 0 < mu omega)
  (hmu1 : ∑ omega, mu omega = 1)
  (hFKG : FKGLatticeCondition mu)
  (hl : ∀ e, e ∈ l)
  (hdiscSub : ∀ k, ∀ x ∈ disc k, x ∈ shell k)
  (hshellDisc : ∀ k, ∀ x ∈ shell k, x ∈ disc k)
  (hoDisc : ∀ k, o ∉ disc k)
  (hcross : ∀ k n, 1 ≤ k → k ≤ n → ∀ omega, ConnOpenSet endU endV omega o (shell n) → ConnOpenSet endU endV omega o (shell k))
  (hn : 1 ≤ n)
  (hD : 0 < D)
  (hsum : ∀ e : E, (∑ k : ↑(Finset.Icc 1 n), (Lindeberg.mean mu (fun omega => if ConnOpenSet endU endV omega (endU e) (shell k) then (1 : Real) else 0) + Lindeberg.mean mu (fun omega => if ConnOpenSet endU endV omega (endV e) (shell k) then (1 : Real) else 0))) ≤ (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
-- imply
  let f : ConfigSpace E → Real := (openCrossEvent endU endV o (shell n)).indicator (fun _ => 1) Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) / D ≤ ∑ e, Lindeberg.cov mu f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.FiniteGraphBoundaryDifferential.hcov_openCross_mass mu hpos hmu1 hFKG endU endV o l hl shell disc hdiscSub hshellDisc hoDisc hcross n hn D hD hsum

/--
[hcov_reindexed_openCross_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FiniteGraphBoundaryDifferential.lean)
-/
@[path]
private lemma hcov_reindexed_openCross_mass_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype E]
  [DecidableEq E]
  [Fintype I]
  [DecidableEq I]
  [Fintype O]
  [DecidableEq O]
  {mu : ConfigSpace O → Real}
  {iota : I → O}
  {endU endV : I → V}
  {o : V}
  {l : List I}
  {shell disc : Nat → Finset V}
  {n : Nat}
  {D : Real}
-- given
  (hpos : ∀ omega, 0 < mu omega)
  (hmu1 : ∑ omega, mu omega = 1)
  (hFKG : FKGLatticeCondition mu)
  (hiota : Function.Injective iota)
  (hl : ∀ e, e ∈ l)
  (hdiscSub : ∀ k, ∀ x ∈ disc k, x ∈ shell k)
  (hshellDisc : ∀ k, ∀ x ∈ shell k, x ∈ disc k)
  (hoDisc : ∀ k, o ∉ disc k)
  (hcross : ∀ k n, 1 ≤ k → k ≤ n → ∀ omega, ConnOpenSet endU endV omega o (shell n) → ConnOpenSet endU endV omega o (shell k))
  (hn : 1 ≤ n)
  (hD : 0 < D)
  (hsum : ∀ e : I, (∑ k : ↑(Finset.Icc 1 n), (Lindeberg.mean mu (fun omega => if ConnOpenSet endU endV (restrictConfig iota omega) (endU e) (shell k) then (1 : Real) else 0) + Lindeberg.mean mu (fun omega => if ConnOpenSet endU endV (restrictConfig iota omega) (endV e) (shell k) then (1 : Real) else 0))) ≤ (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
-- imply
  let f : ConfigSpace O → Real := fun omega => (openCrossEvent endU endV o (shell n)).indicator (fun _ => 1) (restrictConfig iota omega) Lindeberg.mean mu f * (1 - Lindeberg.mean mu f) / D ≤ ∑ e, Lindeberg.cov mu f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.FiniteGraphBoundaryDifferential.hcov_reindexed_openCross_mass mu hpos hmu1 hFKG iota hiota endU endV o l hl shell disc hdiscSub hshellDisc hoDisc hcross n hn D hD hsum

/--
[activeBC_openCross_differential_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FiniteGraphBoundaryDifferential.lean)
-/
@[path]
private lemma activeBC_openCross_differential_inequality_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype E]
  [DecidableEq E]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Nonempty G.edgeSet]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {J : Sym2 V → Real}
  {q beta beta0 : Real}
  {endU endV : G.edgeSet → V}
  {o : V}
  {l : List G.edgeSet}
  {shell disc : Nat → Finset V}
  {n : Nat}
  {D : Real}
-- given
  (hJ : ∀ e, 0 < J e)
  (hq : 1 ≤ q)
  (hbeta : 0 < beta)
  (hbeta0 : beta ≤ beta0)
  (hcoh : ∀ e, e.1 = s(endU e, endV e))
  (hl : ∀ e, e ∈ l)
  (hdiscSub : ∀ k, ∀ x ∈ disc k, x ∈ shell k)
  (hshellDisc : ∀ k, ∀ x ∈ shell k, x ∈ disc k)
  (hoDisc : ∀ k, o ∉ disc k)
  (hcross : ∀ k n, 1 ≤ k → k ≤ n → ∀ omega, ConnOpenSet endU endV omega o (shell n) → ConnOpenSet endU endV omega o (shell k))
  (hn : 1 ≤ n)
  (hD : 0 < D)
  (hsum : ∀ e : G.edgeSet, (∑ k : ↑(Finset.Icc 1 n), (Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q) (fun omega => if ConnOpenSet endU endV omega (endU e) (shell k) then 1 else 0) + Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q) (fun omega => if ConnOpenSet endU endV omega (endV e) (shell k) then 1 else 0))) ≤ (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
-- imply
  ∃ c : Real, 0 < c ∧ c * (Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q) ((openCrossEvent endU endV o (shell n)).indicator (fun _ => 1)) / D) ≤ deriv (fun b => FK.activeBCProbOf G C (FK.betaParams J b) q (openCrossEvent endU endV o (shell n))) beta := by
-- proof
  apply StatMech.OSSS.FiniteGraphBoundaryDifferential.activeBC_openCross_differential_inequality G C J hJ q beta beta0 hq hbeta hbeta0 endU endV hcoh o l hl shell disc hdiscSub hshellDisc hoDisc hcross n hn D hD hsum


-- created on 2026-10-23
