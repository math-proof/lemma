import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalSimonMass
open Finset Filter Set Topology StatMech StatMech.FrontierA


/--
[continuous_freeCorr_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSimonMass.lean)
-/
@[path]
private lemma continuous_freeCorr_beta_eq
  {d : Nat}
  {S : Finset (Site d)}
-- given
  (a b : {v // v ∈ S}) :
-- imply
  Continuous (fun beta ↦ freeCorr d beta S a b) := by
-- proof
  apply StatMech.FrontierA.continuous_freeCorr_beta d S a b

/--
[continuous_corrOriginInner_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSimonMass.lean)
-/
@[path]
private lemma continuous_corrOriginInner_beta_eq
  {d : Nat}
  {S : Finset (Site d)}
  {x : Site d} :
-- imply
  Continuous (fun beta ↦ corrOriginInner d beta S x) := by
-- proof
  apply StatMech.FrontierA.continuous_corrOriginInner_beta d S x

/--
[continuous_phiIsing_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSimonMass.lean)
-/
@[path]
private lemma continuous_phiIsing_beta_eq
  {d : Nat}
  {S : Finset (Site d)} :
-- imply
  Continuous (fun beta ↦ phiIsing d beta S) := by
-- proof
  apply StatMech.FrontierA.continuous_phiIsing_beta d S

/--
[phiIsing_ge_one_at_tildeBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSimonMass.lean)
-/
@[path]
private lemma phiIsing_ge_one_at_tildeBetaC_eq
  {d : Nat}
  {S : Finset (Site d)}
-- given
  (hbdd : BddAbove (tildeBetaCIsingSet d))
  (hS : Percolation.origin d ∈ S) :
-- imply
  1 ≤ phiIsing d (tildeBetaCIsing d) S := by
-- proof
  apply StatMech.FrontierA.phiIsing_ge_one_at_tildeBetaC d hbdd S hS

/--
[isingBetaC_eq_of_strict_transition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSimonMass.lean)
-/
@[path]
private lemma isingBetaC_eq_of_strict_transition_eq
  {d : Nat}
  {t : Real}
-- given
  (ht : 0 < t)
  (hbcpos : 0 < Ising.betaC d)
  (hbelow : ∀ beta, 0 < beta → beta < t → magnetization d beta = 0)
  (habove : ∀ beta, t < beta → 0 < magnetization d beta) :
-- imply
  Ising.betaC d = t := by
-- proof
  apply StatMech.FrontierA.isingBetaC_eq_of_strict_transition d t ht hbcpos hbelow habove

/--
[isingFK_betaC_eq_tildeBetaCIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSimonMass.lean)
-/
@[path]
private lemma isingFK_betaC_eq_tildeBetaCIsing_eq
  {d : Nat}
-- given
  (hd : 2 ≤ d) :
-- imply
  IsingFK.betaC (magnetization d) = tildeBetaCIsing d := by
-- proof
  apply StatMech.FrontierA.isingFK_betaC_eq_tildeBetaCIsing hd

/--
[phiIsing_ge_one_at_isingFK_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSimonMass.lean)
-/
@[path]
private lemma phiIsing_ge_one_at_isingFK_betaC_eq
  {d : Nat}
  {S : Finset (Site d)}
-- given
  (hd : 2 ≤ d)
  (hS : Percolation.origin d ∈ S) :
-- imply
  1 ≤ phiIsing d (IsingFK.betaC (magnetization d)) S := by
-- proof
  apply StatMech.FrontierA.phiIsing_ge_one_at_isingFK_betaC hd S hS


-- created on 2026-10-23
