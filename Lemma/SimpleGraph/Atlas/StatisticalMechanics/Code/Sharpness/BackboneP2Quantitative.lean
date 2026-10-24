import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.BackboneP2Quantitative
open SimpleGraph Finset StatMech StatMech.Sharpness


/--
[shb_isBackboneOf_of_select_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2Quantitative.lean)
-/
@[path]
private lemma shb_isBackboneOf_of_select_eq_some_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V}
  {omega : G.Path x y}
-- given
  (hsel : shb_backboneSelect G n x y = some omega) :
-- imply
  shb_IsBackboneOf G n x y omega := by
-- proof
  apply StatMech.Sharpness.shb_isBackboneOf_of_select_eq_some G n x y omega hsel

/--
[shb_sources_removePath_eq_empty_of_select](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2Quantitative.lean)
-/
@[path]
private lemma shb_sources_removePath_eq_empty_of_select_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V}
  {omega : G.Path x y}
-- given
  (hxy : Not (x = y))
  (hsrc : sources G n = {x, y})
  (hsel : shb_backboneSelect G n x y = some omega) :
-- imply
  sources G (removeWalk n omega.1) = ∅ := by
-- proof
  apply StatMech.Sharpness.shb_sources_removePath_eq_empty_of_select G n omega hxy hsrc hsel

/--
[shb_removeWalk_add_edgeSet_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2Quantitative.lean)
-/
@[path]
private lemma shb_removeWalk_add_edgeSet_of_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph V}
  {n : Current V}
  {x y : V}
  {w : H.Walk x y}
-- given
  (hw : w.IsPath)
  (hodd : ∀ e ∈ w.edges, Odd (n e)) :
-- imply
  (fun e => removeWalk n w e + (if e ∈ w.edges.toFinset then 1 else 0)) = n := by
-- proof
  apply StatMech.Sharpness.shb_removeWalk_add_edgeSet_of_odd G w hw hodd

/--
[shb_removePath_add_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2Quantitative.lean)
-/
@[path]
private lemma shb_removePath_add_edgeSet_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V}
  {omega : G.Path x y}
-- given
  (hbackbone : shb_IsBackboneOf G n x y omega) :
-- imply
  (fun e => removeWalk n omega.1 e + (if e ∈ omega.1.edges.toFinset then 1 else 0)) = n := by
-- proof
  apply StatMech.Sharpness.shb_removePath_add_edgeSet G omega hbackbone

/--
[shb_weight_removeWalk_factor_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2Quantitative.lean)
-/
@[path]
private lemma shb_weight_removeWalk_factor_of_odd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {H : SimpleGraph V}
  {n : Current V}
  {x y : V}
  {w : H.Walk x y}
-- given
  (J : Sym2 V -> Real)
  (hw : w.IsPath)
  (hodd : ∀ e ∈ w.edges, Odd (n e)) :
-- imply
  weight G beta J n = weight G beta J (removeWalk n w) * ∏ e ∈ G.edgeFinset, (if e ∈ w.edges.toFinset then (beta * J e) / (removeWalk n w e + 1) else 1) := by
-- proof
  apply StatMech.Sharpness.shb_weight_removeWalk_factor_of_odd G beta J w hw hodd

/--
[shb_weight_removePath_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2Quantitative.lean)
-/
@[path]
private lemma shb_weight_removePath_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {n : Current V}
  {x y : V}
  {omega : G.Path x y}
-- given
  (J : Sym2 V -> Real)
  (hbackbone : shb_IsBackboneOf G n x y omega) :
-- imply
  weight G beta J n = weight G beta J (removeWalk n omega.1) * ∏ e ∈ G.edgeFinset, (if e ∈ omega.1.edges.toFinset then (beta * J e) / (removeWalk n omega.1 e + 1) else 1) := by
-- proof
  apply StatMech.Sharpness.shb_weight_removePath_factor G beta J omega hbackbone

/--
[shb_P2_current_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2Quantitative.lean)
-/
@[path]
private lemma shb_P2_current_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {n : Current V}
  {x y : V}
  {p : IsBackbonePath G n x y}
-- given
  (J : Sym2 V -> Real)
  (hxy : Not (x = y))
  (hsrc : sources G n = {x, y}) :
-- imply
  sources G (removeWalk n p.1) = ∅ ∧ weight G beta J n = weight G beta J (removeWalk n p.1) * ∏ e ∈ G.edgeFinset, (if e ∈ p.1.edges.toFinset then (beta * J e) / (removeWalk n p.1 e + 1) else 1) := by
-- proof
  apply StatMech.Sharpness.shb_P2_current_factor G beta J p hxy hsrc

/--
[shb_backboneNum_eq_removeWalk_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2Quantitative.lean)
-/
@[path]
private lemma shb_backboneNum_eq_removeWalk_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {x y : V}
  {omega : G.Path x y}
-- given
  (J : Sym2 V -> Real) :
-- imply
  shb_backboneNum G beta J x y omega = ∑' m : G.edgeFinset -> Nat, if sources G (ofEdgeFun G m) = {x, y} ∧ shb_backboneSelect G (ofEdgeFun G m) x y = some omega then weight G beta J (removeWalk (ofEdgeFun G m) omega.1) * ∏ e ∈ G.edgeFinset, (if e ∈ omega.1.edges.toFinset then (beta * J e) / (removeWalk (ofEdgeFun G m) omega.1 e + 1) else 1) else 0 := by
-- proof
  apply StatMech.Sharpness.shb_backboneNum_eq_removeWalk_sum G beta J omega

/--
[shb_rho_eq_removeWalk_sum_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2Quantitative.lean)
-/
@[path]
private lemma shb_rho_eq_removeWalk_sum_div_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {x y : V}
  {omega : G.Path x y}
-- given
  (J : Sym2 V -> Real) :
-- imply
  shb_rho G beta J x y omega = (∑' m : G.edgeFinset -> Nat, if sources G (ofEdgeFun G m) = {x, y} ∧ shb_backboneSelect G (ofEdgeFun G m) x y = some omega then weight G beta J (removeWalk (ofEdgeFun G m) omega.1) * ∏ e ∈ G.edgeFinset, (if e ∈ omega.1.edges.toFinset then (beta * J e) / (removeWalk (ofEdgeFun G m) omega.1 e + 1) else 1) else 0) / currentSum G beta J ∅ := by
-- proof
  apply StatMech.Sharpness.shb_rho_eq_removeWalk_sum_div G beta J omega


-- created on 2026-10-23
