import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kwd_lotempexpansion
open Finset StatMech StatMech.Walls


/--
[kwd_bond_eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_lotempexpansion.lean)
-/
@[path]
private lemma kwd_bond_eq_one_or_neg_one_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  bond s e = 1 ∨ bond s e = -1 := by
-- proof
  apply StatMech.Walls.kwd_bond_eq_one_or_neg_one s e

/--
[kwd_sum_bond_eq_card_sub_two_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_lotempexpansion.lean)
-/
@[path]
private lemma kwd_sum_bond_eq_card_sub_two_cut_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V} :
-- imply
  (∑ e ∈ G.edgeFinset, bond s e) = (G.edgeFinset.card : ℝ) - 2 * (kwdCutEdges G s).card := by
-- proof
  apply StatMech.Walls.kwd_sum_bond_eq_card_sub_two_cut s

/--
[kwd_isingZ_low_temp_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_lotempexpansion.lean)
-/
@[path]
private lemma kwd_isingZ_low_temp_expansion_eq
  [Fintype V]
  [DecidableEq V]
  {β : ℝ} :
-- imply
  isingZ G β 0 = Real.exp (β * G.edgeFinset.card) * ∑ s : ConfigSpace V, Real.exp (-2 * β) ^ (kwdCutEdges G s).card := by
-- proof
  apply StatMech.Walls.kwd_isingZ_low_temp_expansion β

/--
[kwd_isingWeight_eq_contour_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_lotempexpansion.lean)
-/
@[path]
private lemma kwd_isingWeight_eq_contour_weight_eq
  [Fintype V]
  [DecidableEq V]
  {β : ℝ}
  {s : ConfigSpace V} :
-- imply
  isingWeight G β 0 s = Real.exp (β * G.edgeFinset.card) * Real.exp (-2 * β) ^ (kwdCutEdges G s).card := by
-- proof
  apply StatMech.Walls.kwd_isingWeight_eq_contour_weight β s

/--
[kwd_bond_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_lotempexpansion.lean)
-/
@[path]
private lemma kwd_bond_flip_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  bond (fun v => ! s v) e = bond s e := by
-- proof
  apply StatMech.Walls.kwd_bond_flip s e

/--
[kwd_cutEdges_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_lotempexpansion.lean)
-/
@[path]
private lemma kwd_cutEdges_flip_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V} :
-- imply
  kwdCutEdges G (fun v => ! s v) = kwdCutEdges G s := by
-- proof
  apply StatMech.Walls.kwd_cutEdges_flip s


-- created on 2026-10-23
