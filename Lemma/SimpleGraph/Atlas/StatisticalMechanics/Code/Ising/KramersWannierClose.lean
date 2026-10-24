import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.KramersWannierClose
open Finset StatMech StatMech.Ising


/--
[sum_bond_eq_card_sub_two_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierClose.lean)
-/
@[path]
private lemma sum_bond_eq_card_sub_two_cut_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V} :
-- imply
  (∑ e ∈ G.edgeFinset, bond s e) = (G.edgeFinset.card : ℝ) - 2 * (cutEdges G s).card := by
-- proof
  apply StatMech.Ising.sum_bond_eq_card_sub_two_cut s

/--
[isingZ_low_temp_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierClose.lean)
-/
@[path]
private lemma isingZ_low_temp_expansion_eq
  [Fintype V]
  [DecidableEq V]
  {β : ℝ} :
-- imply
  isingZ G β 0 = Real.exp (β * G.edgeFinset.card) * ∑ s : ConfigSpace V, Real.exp (-2 * β) ^ (cutEdges G s).card := by
-- proof
  apply StatMech.Ising.isingZ_low_temp_expansion β

/--
[bond_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierClose.lean)
-/
@[path]
private lemma bond_flip_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  bond (fun v => ! s v) e = bond s e := by
-- proof
  apply StatMech.Ising.bond_flip s e

/--
[cutEdges_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierClose.lean)
-/
@[path]
private lemma cutEdges_flip_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V} :
-- imply
  cutEdges G (fun v => ! s v) = cutEdges G s := by
-- proof
  apply StatMech.Ising.cutEdges_flip s

/--
[dualContourMatching_of_cutMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierClose.lean)
-/
@[path]
private lemma dualContourMatching_of_cutMatching_eq
  [Fintype V]
  [DecidableEq V]
  {β βstar mult : ℝ}
-- given
  (hmult : mult ≠ 0)
  (htemp : Real.tanh βstar = Real.exp (-2 * β))
  (hmatch : CutEvenSubgraphMatching Gp Gd (Real.exp (-2 * β)) mult) :
-- imply
  DualContourMatching Gp Gd β βstar ((2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card / (Real.exp (β * Gp.edgeFinset.card) * mult)) := by
-- proof
  apply StatMech.Ising.dualContourMatching_of_cutMatching β βstar mult hmult htemp hmatch

/--
[isingZ_self_dual_of_cutMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierClose.lean)
-/
@[path]
private lemma isingZ_self_dual_of_cutMatching_eq
  [Fintype V]
  [DecidableEq V]
  {β βstar mult : ℝ}
-- given
  (hmult : mult ≠ 0)
  (htemp : Real.tanh βstar = Real.exp (-2 * β))
  (hmatch : CutEvenSubgraphMatching Gp Gd (Real.exp (-2 * β)) mult) :
-- imply
  isingZ Gd βstar 0 = ((2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card / (Real.exp (β * Gp.edgeFinset.card) * mult)) * isingZ Gp β 0 := by
-- proof
  apply StatMech.Ising.isingZ_self_dual_of_cutMatching β βstar mult hmult htemp hmatch


-- created on 2026-10-23
