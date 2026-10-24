import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv
open Finset StatMech StatMech.FK


/--
[restrictActive_extendActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEquiv.lean)
-/
@[path]
private lemma restrictActive_extendActive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {omega : ConfigSpace G.edgeSet} :
-- imply
  restrictActive G (extendActive G omega) = omega := by
-- proof
  apply StatMech.FK.restrictActive_extendActive G C omega

/--
[restrictActive_activeSplitEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEquiv.lean)
-/
@[path]
private lemma restrictActive_activeSplitEquiv_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {eta : ConfigSpace G.edgeSet}
-- given
  (xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet}) :
-- imply
  restrictActive G ((activeSplitEquiv G).symm (eta, xi)) = eta := by
-- proof
  apply StatMech.FK.restrictActive_activeSplitEquiv_symm G C eta xi

/--
[numClustersBC_eq_of_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEquiv.lean)
-/
@[path]
private lemma numClustersBC_eq_of_edges_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {omega eta : ConfigSpace (Sym2 V)}
-- given
  (h : ∀ e ∈ G.edgeFinset, omega e = eta e) :
-- imply
  numClustersBC G C omega = numClustersBC G C eta := by
-- proof
  apply StatMech.FK.numClustersBC_eq_of_edges G C omega eta h

/--
[bcWeight_eq_of_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEquiv.lean)
-/
@[path]
private lemma bcWeight_eq_of_edges_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : Real}
  {omega eta : ConfigSpace (Sym2 V)}
-- given
  (h : ∀ e ∈ G.edgeFinset, omega e = eta e) :
-- imply
  bcWeight G C p q omega = bcWeight G C p q eta := by
-- proof
  apply StatMech.FK.bcWeight_eq_of_edges G C p q omega eta h

/--
[activeBCWeight_const_eq_bcWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEquiv.lean)
-/
@[path]
private lemma activeBCWeight_const_eq_bcWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : Real}
  {omega : ConfigSpace G.edgeSet} :
-- imply
  activeBCWeight G C (fun _ => p) q omega = bcWeight G C p q (extendActive G omega) := by
-- proof
  apply StatMech.FK.activeBCWeight_const_eq_bcWeight G C p q omega

/--
[bcWeight_activeSplitEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEquiv.lean)
-/
@[path]
private lemma bcWeight_activeSplitEquiv_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : Real}
  {eta : ConfigSpace G.edgeSet}
-- given
  (xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet}) :
-- imply
  bcWeight G C p q ((activeSplitEquiv G).symm (eta, xi)) = activeBCWeight G C (fun _ => p) q eta := by
-- proof
  apply StatMech.FK.bcWeight_activeSplitEquiv_symm G C p q eta xi

/--
[card_inactive_config](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEquiv.lean)
-/
@[path]
private lemma card_inactive_config_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj] :
-- imply
  Fintype.card (ConfigSpace {e : Sym2 V // e ∉ G.edgeSet}) = 2 ^ ecz_NE G := by
-- proof
  apply StatMech.FK.card_inactive_config G C

/--
[activeBCZ_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEquiv.lean)
-/
@[path]
private lemma activeBCZ_factorization_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : Real} :
-- imply
  bcZ G C p q = 2 ^ ecz_NE G * activeBCZ G C (fun _ => p) q := by
-- proof
  apply StatMech.FK.activeBCZ_factorization G C p q

/--
[activeBCNumer_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEquiv.lean)
-/
@[path]
private lemma activeBCNumer_factorization_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : Real}
-- given
  (f : ConfigSpace G.edgeSet -> Real) :
-- imply
  (∑ omega : ConfigSpace (Sym2 V), f (restrictActive G omega) * bcWeight G C p q omega) = 2 ^ ecz_NE G * activeBCNumer G C (fun _ => p) q f := by
-- proof
  apply StatMech.FK.activeBCNumer_factorization G C p q f

/--
[activeBCMean_eq_bcProb_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEquiv.lean)
-/
@[path]
private lemma activeBCMean_eq_bcProb_lift_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (f : ConfigSpace G.edgeSet -> Real) :
-- imply
  activeBCMean G C (fun _ => p) q f = ∑ omega : ConfigSpace (Sym2 V), f (restrictActive G omega) * bcProb G C p q omega := by
-- proof
  apply StatMech.FK.activeBCMean_eq_bcProb_lift G C hp hp1 hq f

/--
[activeBCProbOf_eq_bcProb_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEquiv.lean)
-/
@[path]
private lemma activeBCProbOf_eq_bcProb_preimage_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {p q : Real}
  {A : Set (ConfigSpace G.edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  activeBCProbOf G C (fun _ => p) q A = ∑ omega : ConfigSpace (Sym2 V), (restrictActive G ⁻¹' A).indicator (fun _ => (1 : Real)) omega * bcProb G C p q omega := by
-- proof
  apply StatMech.FK.activeBCProbOf_eq_bcProb_preimage G C hp hp1 hq A

/--
[activeBCMean_boundaryClique_eq_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEquiv.lean)
-/
@[path]
private lemma activeBCMean_boundaryClique_eq_wired_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidablePred bdry]
  {p q : Real}
-- given
  (bdry : V -> Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (f : ConfigSpace G.edgeSet -> Real) :
-- imply
  activeBCMean G (Lattice.boundaryCliqueGraph bdry) (fun _ => p) q f = ∑ omega : ConfigSpace (Sym2 V), f (restrictActive G omega) * wiredFkProb G bdry p q omega := by
-- proof
  apply StatMech.FK.activeBCMean_boundaryClique_eq_wired G C bdry hp hp1 hq f

/--
[activeBCProbOf_boundaryClique_eq_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEquiv.lean)
-/
@[path]
private lemma activeBCProbOf_boundaryClique_eq_wired_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidablePred bdry]
  {p q : Real}
  {A : Set (ConfigSpace G.edgeSet)}
-- given
  (bdry : V -> Prop)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  activeBCProbOf G (Lattice.boundaryCliqueGraph bdry) (fun _ => p) q A = ∑ omega : ConfigSpace (Sym2 V), (restrictActive G ⁻¹' A).indicator (fun _ => (1 : Real)) omega * wiredFkProb G bdry p q omega := by
-- proof
  apply StatMech.FK.activeBCProbOf_boundaryClique_eq_wired G C bdry hp hp1 hq A


-- created on 2026-10-23
