import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.ActiveBoundaryDifferential
open Finset Set StatMech StatMech.OSSS StatMech.OSSS.ActiveBoundaryDifferential


/--
[cov_activeBC_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ActiveBoundaryDifferential.lean)
-/
@[path]
private lemma cov_activeBC_eq_eq
  [Fintype V]
  [DecidableEq V]
  {d : Nat}
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {q : Real}
-- given
  (pf : Sym2 V -> Real)
  (f g : ConfigSpace G.edgeSet -> Real) :
-- imply
  Lindeberg.cov (FK.activeBCProb G C pf q) f g = FK.activeBCCov G C pf q f g := by
-- proof
  apply StatMech.OSSS.ActiveBoundaryDifferential.cov_activeBC_eq G C pf q f g

/--
[activeBC_cross_one_sub_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ActiveBoundaryDifferential.lean)
-/
@[path]
private lemma activeBC_cross_one_sub_lower_eq
  [Fintype V]
  [DecidableEq V]
  {d : Nat}
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {q beta beta0 : Real}
  {edge : G.edgeSet -> Sym2 (Site d)}
  {endU endV : G.edgeSet -> Site d}
  {o : Site d}
  {B : Set (Site d)}
-- given
  (J : Sym2 V -> Real)
  (hJ : forall e, 0 < J e)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0)
  (hcoh : forall e, edge e = s(endU e, endV e))
  (hoB : o ∉ B) :
-- imply
  (incidentEdges endU endV o).prod (fun e => Real.exp (-(beta0 * J e.1))) <= 1 - Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q) ((crossEvent edge o B).indicator fun _ => (1 : Real)) := by
-- proof
  apply StatMech.OSSS.ActiveBoundaryDifferential.activeBC_cross_one_sub_lower G C J hJ q beta beta0 hq hbeta hbeta0 hcoh o B hoB

/--
[activeBC_fk_differential_logistic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ActiveBoundaryDifferential.lean)
-/
@[path]
private lemma activeBC_fk_differential_logistic_eq
  [Fintype V]
  [DecidableEq V]
  {d : Nat}
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Nonempty G.edgeSet]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {q beta : Real}
  {edge : G.edgeSet -> Sym2 (Site d)}
  {endU endV : G.edgeSet -> Site d}
  {o : Site d}
  {l : List G.edgeSet}
  {n : Nat}
  {Lambda : Finset (Site d)}
-- given
  (J : Sym2 V -> Real)
  (hJ : forall e, 0 < J e)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hinj : Function.Injective edge)
  (hcoh : forall e, edge e = s(endU e, endV e))
  (hadj : forall e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hl : forall e, e ∈ l)
  (disc0 : Nat -> Finset (Site d))
  (hdisc0sub : ∀ k, ∀ x ∈ disc0 k, x ∈ vertexBoundary d k)
  (hdisc0sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc0 k)
  (hoB : forall k, o ∉ disc0 k)
  (ho : forall k : Nat, 1 <= k -> o ∈ box d (k - 1))
  (hn : 1 <= n)
  (hne : Lambda.Nonempty)
  (hLu : forall e : G.edgeSet, endU e ∈ Lambda)
  (hLv : forall e : G.edgeSet, endV e ∈ Lambda)
  (hUbox : forall e : G.edgeSet, endU e ∈ box d n)
  (hVbox : forall e : G.edgeSet, endV e ∈ box d n) :
-- imply
  exists cR : Real, 0 < cR ∧ cR * (Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q) (crossIndG edge o n) * (1 - Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q) (crossIndG edge o n)) / (4 * Lambda.sup' hne (fun x => ∑ j ∈ Finset.range n, Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q) (fun omega => if ConnectedToSet d (liftCfg edge omega) x (centeredBoundary x j) then (1 : Real) else 0)) / (n : Real))) <= deriv (fun b => FK.activeBCProbOf G C (FK.betaParams J b) q (crossEvent edge o (vertexBoundary d n))) beta := by
-- proof
  apply StatMech.OSSS.ActiveBoundaryDifferential.activeBC_fk_differential_logistic G C J hJ q beta hq hbeta hinj hcoh hadj o l hl disc0 hdisc0sub hdisc0sup hoB ho n hn Lambda hne hLu hLv hUbox hVbox

/--
[activeBC_fk_differential_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ActiveBoundaryDifferential.lean)
-/
@[path]
private lemma activeBC_fk_differential_inequality_eq
  [Fintype V]
  [DecidableEq V]
  {d : Nat}
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Nonempty G.edgeSet]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {q beta beta0 : Real}
  {edge : G.edgeSet -> Sym2 (Site d)}
  {endU endV : G.edgeSet -> Site d}
  {o : Site d}
  {l : List G.edgeSet}
  {n : Nat}
  {Lambda : Finset (Site d)}
-- given
  (J : Sym2 V -> Real)
  (hJ : forall e, 0 < J e)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0)
  (hinj : Function.Injective edge)
  (hcoh : forall e, edge e = s(endU e, endV e))
  (hadj : forall e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hl : forall e, e ∈ l)
  (disc0 : Nat -> Finset (Site d))
  (hdisc0sub : ∀ k, ∀ x ∈ disc0 k, x ∈ vertexBoundary d k)
  (hdisc0sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc0 k)
  (hoB : forall k, o ∉ disc0 k)
  (ho : forall k : Nat, 1 <= k -> o ∈ box d (k - 1))
  (hn : 1 <= n)
  (hne : Lambda.Nonempty)
  (hLu : forall e : G.edgeSet, endU e ∈ Lambda)
  (hLv : forall e : G.edgeSet, endV e ∈ Lambda)
  (hUbox : forall e : G.edgeSet, endU e ∈ box d n)
  (hVbox : forall e : G.edgeSet, endV e ∈ box d n) :
-- imply
  exists c : Real, 0 < c ∧ c * (Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q) (crossIndG edge o n) / (4 * Lambda.sup' hne (fun x => ∑ j ∈ Finset.range n, Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q) (fun omega => if ConnectedToSet d (liftCfg edge omega) x (centeredBoundary x j) then (1 : Real) else 0)) / (n : Real))) <= deriv (fun b => FK.activeBCProbOf G C (FK.betaParams J b) q (crossEvent edge o (vertexBoundary d n))) beta := by
-- proof
  apply StatMech.OSSS.ActiveBoundaryDifferential.activeBC_fk_differential_inequality G C J hJ q beta beta0 hq hbeta hbeta0 hinj hcoh hadj o l hl disc0 hdisc0sub hdisc0sup hoB ho n hn Lambda hne hLu hLv hUbox hVbox


-- created on 2026-10-23
