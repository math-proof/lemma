import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
open Finset StatMech StatMech.Ising StatMech.Sharpness


/--
[wJ_edgeFinset_const_eq_isingWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeDomain.lean)
-/
@[path]
private lemma wJ_edgeFinset_const_eq_isingWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
-- given
  (beta h : ℝ) :
-- imply
  wJ G.edgeFinset (fun _ => beta) (fun _ => beta * h) s = isingWeight G beta h s := by
-- proof
  apply StatMech.Ising.wJ_edgeFinset_const_eq_isingWeight G beta h s

/--
[ZJ_edgeFinset_const_eq_isingZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeDomain.lean)
-/
@[path]
private lemma ZJ_edgeFinset_const_eq_isingZ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (beta h : ℝ) :
-- imply
  ZJ G.edgeFinset (fun _ => beta) (fun _ => beta * h) = isingZ G beta h := by
-- proof
  apply StatMech.Ising.ZJ_edgeFinset_const_eq_isingZ G beta h

/--
[isingExpectation_spin_eq_expJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeDomain.lean)
-/
@[path]
private lemma isingExpectation_spin_eq_expJ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {z : V}
-- given
  (beta h : ℝ) :
-- imply
  isingExpectation G beta h (fun s => spin s z) = expJ G.edgeFinset (fun _ => beta) (fun _ => beta * h) (spinProd {z}) := by
-- proof
  apply StatMech.Ising.isingExpectation_spin_eq_expJ G beta h z

/--
[isingExpectation_spinProd_eq_expJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeDomain.lean)
-/
@[path]
private lemma isingExpectation_spinProd_eq_expJ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (beta h : ℝ) :
-- imply
  isingExpectation G beta h (spinProd A) = expJ G.edgeFinset (fun _ => beta) (fun _ => beta * h) (spinProd A) := by
-- proof
  apply StatMech.Ising.isingExpectation_spinProd_eq_expJ G beta h A

/--
[isingExpectation_spin_mono_graph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeDomain.lean)
-/
@[path]
private lemma isingExpectation_spin_mono_graph_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {z : V}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hGH : G ≤ H) :
-- imply
  isingExpectation G beta h (fun s => spin s z) ≤ isingExpectation H beta h (fun s => spin s z) := by
-- proof
  apply StatMech.Ising.isingExpectation_spin_mono_graph G H beta h hbeta hh hGH z

/--
[isingExpectation_spin_induce_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeDomain.lean)
-/
@[path]
private lemma isingExpectation_spin_induce_le_eq
  [Fintype U]
  [DecidableEq U]
  {K : SimpleGraph U}
  [DecidableRel K.Adj]
  [DecidablePred P]
  {x : {u // P u}}
-- given
  (P : U → Prop)
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  isingExpectation (K.comap (Subtype.val : {u // P u} → U)) beta h (fun s => spin s x) ≤ isingExpectation K beta h (fun s => spin s x.1) := by
-- proof
  apply StatMech.Sharpness.isingExpectation_spin_induce_le K P beta h hbeta hh x


-- created on 2026-10-23
