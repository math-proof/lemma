import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.EdgeSubsetDomainMarkov.Part5
open Finset SimpleGraph StatMech StatMech.FK


/--
[edgeSubsetFibreConfig_agreesOff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean)
-/
@[path]
private lemma edgeSubsetFibreConfig_agreesOff_eq
  [Fintype V]
  [DecidableEq V]
  {K : SimpleGraph V}
  [DecidableRel K.Adj]
  {psi : ConfigSpace (Sym2 V)}
  {eta : ConfigSpace K.edgeSet} :
-- imply
  AgreesOff K.edgeFinset psi (edgeSubsetFibreConfig K psi eta) := by
-- proof
  apply StatMech.FK.edgeSubsetFibreConfig_agreesOff K psi eta

/--
[edgeSubsetFibreConfig_restrictActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean)
-/
@[path]
private lemma edgeSubsetFibreConfig_restrictActive_eq
  [Fintype V]
  [DecidableEq V]
  {K : SimpleGraph V}
  [DecidableRel K.Adj]
  {psi : ConfigSpace (Sym2 V)}
  {eta : ConfigSpace K.edgeSet} :
-- imply
  restrictActive K (edgeSubsetFibreConfig K psi eta) = eta := by
-- proof
  apply StatMech.FK.edgeSubsetFibreConfig_restrictActive K psi eta

/--
[edgeSubsetFibreConfig_restrictActive_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean)
-/
@[path]
private lemma edgeSubsetFibreConfig_restrictActive_eq_eq
  [Fintype V]
  [DecidableEq V]
  {K : SimpleGraph V}
  [DecidableRel K.Adj]
  {psi rho : ConfigSpace (Sym2 V)}
-- given
  (hrho : AgreesOff K.edgeFinset psi rho) :
-- imply
  edgeSubsetFibreConfig K psi (restrictActive K rho) = rho := by
-- proof
  apply StatMech.FK.edgeSubsetFibreConfig_restrictActive_eq K psi rho hrho

/--
[openSub_edgeSubsetFibre_sup_frozen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean)
-/
@[path]
private lemma openSub_edgeSubsetFibre_sup_frozen_eq
  [Fintype V]
  [DecidableEq V]
  {K H B : SimpleGraph V}
  [DecidableRel K.Adj]
  {psi : ConfigSpace (Sym2 V)}
  {eta : ConfigSpace K.edgeSet}
-- given
  (hKH : K ≤ H) :
-- imply
  openSub H (edgeSubsetFibreConfig K psi eta) ⊔ B = openSub K (extendActive K eta) ⊔ edgeSubsetFrozenExteriorGraph K H B psi := by
-- proof
  apply StatMech.FK.openSub_edgeSubsetFibre_sup_frozen K H B hKH psi eta

/--
[sup_edgeSubsetFrozen_reachable_iff_induced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean)
-/
@[path]
private lemma sup_edgeSubsetFrozen_reachable_iff_induced_eq
  [Fintype V]
  [DecidableEq V]
  {K H B : SimpleGraph V}
  [DecidableRel K.Adj]
  {psi : ConfigSpace (Sym2 V)}
  {A : SimpleGraph V}
  {x y : V} :
-- imply
  (A ⊔ edgeSubsetFrozenExteriorGraph K H B psi).Reachable x y ↔ (A ⊔ edgeSubsetInducedWiring K H B psi).Reachable x y := by
-- proof
  apply StatMech.FK.sup_edgeSubsetFrozen_reachable_iff_induced K H B psi A x y

/--
[numClustersBC_edgeSubsetFibre_eq_induced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean)
-/
@[path]
private lemma numClustersBC_edgeSubsetFibre_eq_induced_eq
  [Fintype V]
  [DecidableEq V]
  {K H B : SimpleGraph V}
  [DecidableRel K.Adj]
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 V)}
  {eta : ConfigSpace K.edgeSet}
-- given
  (hKH : K ≤ H) :
-- imply
  numClustersBC H B (edgeSubsetFibreConfig K psi eta) = numClustersBC K (edgeSubsetInducedWiring K H B psi) (extendActive K eta) := by
-- proof
  apply StatMech.FK.numClustersBC_edgeSubsetFibre_eq_induced K H B hKH psi eta

/--
[edgeProduct_edgeSubsetFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean)
-/
@[path]
private lemma edgeProduct_edgeSubsetFibre_eq
  [Fintype V]
  [DecidableEq V]
  {K H : SimpleGraph V}
  [DecidableRel K.Adj]
  [DecidableRel H.Adj]
  {psi : ConfigSpace (Sym2 V)}
  {p : Real}
  {eta : ConfigSpace K.edgeSet}
-- given
  (hKH : K ≤ H) :
-- imply
  edgeProduct H p (edgeSubsetFibreConfig K psi eta) = edgeSubsetExteriorEdgeFactor K H psi p * edgeProduct K p (extendActive K eta) := by
-- proof
  apply StatMech.FK.edgeProduct_edgeSubsetFibre K H hKH psi p eta

/--
[bcWeight_edgeSubsetFibre_eq_induced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean)
-/
@[path]
private lemma bcWeight_edgeSubsetFibre_eq_induced_eq
  [Fintype V]
  [DecidableEq V]
  {K H B : SimpleGraph V}
  [DecidableRel K.Adj]
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 V)}
  {p q : Real}
  {eta : ConfigSpace K.edgeSet}
-- given
  (hKH : K ≤ H) :
-- imply
  bcWeight H B p q (edgeSubsetFibreConfig K psi eta) = edgeSubsetExteriorEdgeFactor K H psi p * activeBCWeight K (edgeSubsetInducedWiring K H B psi) (fun _ => p) q eta := by
-- proof
  apply StatMech.FK.bcWeight_edgeSubsetFibre_eq_induced K H B hKH psi p q eta

/--
[edgeSubset_inducedBcZ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean)
-/
@[path]
private lemma edgeSubset_inducedBcZ_eq_eq
  [Fintype V]
  [DecidableEq V]
  {K H B : SimpleGraph V}
  [DecidableRel K.Adj]
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 V)}
  {p q : Real}
-- given
  (hKH : K ≤ H) :
-- imply
  inducedBcZ H B p q K.edgeFinset psi = edgeSubsetExteriorEdgeFactor K H psi p * activeBCZ K (edgeSubsetInducedWiring K H B psi) (fun _ => p) q := by
-- proof
  apply StatMech.FK.edgeSubset_inducedBcZ_eq K H B hKH psi p q

/--
[edgeSubsetFibre_condBcProb_eq_activeBCProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean)
-/
@[path]
private lemma edgeSubsetFibre_condBcProb_eq_activeBCProb_eq
  [Fintype V]
  [DecidableEq V]
  {K H B : SimpleGraph V}
  [DecidableRel K.Adj]
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 V)}
  {p q : Real}
  {eta : ConfigSpace K.edgeSet}
-- given
  (hKH : K ≤ H)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  condBcProb H B p q K.edgeFinset psi (edgeSubsetFibreConfig K psi eta) = activeBCProb K (edgeSubsetInducedWiring K H B psi) (fun _ => p) q eta := by
-- proof
  apply StatMech.FK.edgeSubsetFibre_condBcProb_eq_activeBCProb K H B hKH psi hp hp1 eta

/--
[edgeSubsetFibreCondEventMass_eq_activeBCProbOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean)
-/
@[path]
private lemma edgeSubsetFibreCondEventMass_eq_activeBCProbOf_eq
  [Fintype V]
  [DecidableEq V]
  {K H B : SimpleGraph V}
  [DecidableRel K.Adj]
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 V)}
  {p q : Real}
  {A : Set (ConfigSpace K.edgeSet)}
-- given
  (hKH : K ≤ H)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  edgeSubsetFibreCondEventMass K H B psi p q A = activeBCProbOf K (edgeSubsetInducedWiring K H B psi) (fun _ => p) q A := by
-- proof
  apply StatMech.FK.edgeSubsetFibreCondEventMass_eq_activeBCProbOf K H B hKH psi hp hp1 A

/--
[edgeSubsetFibreCondEventMass_eq_bcEventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean)
-/
@[path]
private lemma edgeSubsetFibreCondEventMass_eq_bcEventMass_eq
  [Fintype V]
  [DecidableEq V]
  {K H B : SimpleGraph V}
  [DecidableRel K.Adj]
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 V)}
  {p q : Real}
  {A : Set (ConfigSpace K.edgeSet)}
-- given
  (hKH : K ≤ H)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  edgeSubsetFibreCondEventMass K H B psi p q A = bcEventMass K (edgeSubsetInducedWiring K H B psi) p q (restrictActive K ⁻¹' A) := by
-- proof
  apply StatMech.FK.edgeSubsetFibreCondEventMass_eq_bcEventMass K H B hKH psi hp hp1 hq A

/--
[edgeSubsetFibreCondEventMass_eq_ambientSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean)
-/
@[path]
private lemma edgeSubsetFibreCondEventMass_eq_ambientSum_eq
  [Fintype V]
  [DecidableEq V]
  {K H B : SimpleGraph V}
  [DecidableRel K.Adj]
  [DecidableRel H.Adj]
  [DecidableRel B.Adj]
  {psi : ConfigSpace (Sym2 V)}
  {p q : Real}
  {A : Set (ConfigSpace K.edgeSet)} :
-- imply
  edgeSubsetFibreCondEventMass K H B psi p q A = ∑ rho, (restrictActive K ⁻¹' A).indicator (fun _ => (1 : Real)) rho * condBcProb H B p q K.edgeFinset psi rho := by
-- proof
  apply StatMech.FK.edgeSubsetFibreCondEventMass_eq_ambientSum K H B psi p q A


-- created on 2026-10-23
