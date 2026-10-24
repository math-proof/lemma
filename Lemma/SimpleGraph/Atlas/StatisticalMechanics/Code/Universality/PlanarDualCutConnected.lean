import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.PlanarDualCutConnected
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[pdc_barrierGraphPrimal_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_barrierGraphPrimal_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {a b : Site 2} :
-- imply
  (pdc_barrierGraphPrimal ω n).Adj a b ↔ ∃ v w : Site 2, dcw_isBarrierEdge ω n v w ∧ ((a = v ∧ b = w) ∨ (a = w ∧ b = v)) := by
-- proof
  apply StatMech.Universality.pdc_barrierGraphPrimal_adj ω n a b

/--
[pdc_rot90_adj_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_rot90_adj_dual_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {a b : Site 2}
-- given
  (h : (pdc_barrierGraphPrimal ω n).Adj a b) :
-- imply
  (dcw_dualBarrierGraph ω n).Adj (rot90Fun a) (rot90Fun b) := by
-- proof
  apply StatMech.Universality.pdc_rot90_adj_dual ω n h

/--
[pdc_rot90Hom_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_rot90Hom_apply_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {a : Site 2} :
-- imply
  pdc_rot90Hom ω n a = rot90Fun a := by
-- proof
  apply StatMech.Universality.pdc_rot90Hom_apply ω n a

/--
[pdc_rot90Inv_adj_primal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_rot90Inv_adj_primal_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {p q : Site 2}
-- given
  (h : (dcw_dualBarrierGraph ω n).Adj p q) :
-- imply
  (pdc_barrierGraphPrimal ω n).Adj (rot90Inv p) (rot90Inv q) := by
-- proof
  apply StatMech.Universality.pdc_rot90Inv_adj_primal ω n h

/--
[pdc_rot90InvHom_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_rot90InvHom_apply_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {p : Site 2} :
-- imply
  pdc_rot90InvHom ω n p = rot90Inv p := by
-- proof
  apply StatMech.Universality.pdc_rot90InvHom_apply ω n p

/--
[pdc_rot90Inv_rot90Fun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_rot90Inv_rot90Fun_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x : Site 2} :
-- imply
  rot90Inv (rot90Fun x) = x := by
-- proof
  apply StatMech.Universality.pdc_rot90Inv_rot90Fun x

/--
[pdc_dualReach_of_primalReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_dualReach_of_primalReach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {a b : Site 2}
-- given
  (h : (pdc_barrierGraphPrimal ω n).Reachable a b) :
-- imply
  (dcw_dualBarrierGraph ω n).Reachable (rot90Fun a) (rot90Fun b) := by
-- proof
  apply StatMech.Universality.pdc_dualReach_of_primalReach ω n h

/--
[pdc_primalReach_of_dualReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_primalReach_of_dualReach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {p q : Site 2}
-- given
  (h : (dcw_dualBarrierGraph ω n).Reachable p q) :
-- imply
  (pdc_barrierGraphPrimal ω n).Reachable (rot90Inv p) (rot90Inv q) := by
-- proof
  apply StatMech.Universality.pdc_primalReach_of_dualReach ω n h

/--
[pdc_dualReach_iff_primalReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_dualReach_iff_primalReach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {a b : Site 2} :
-- imply
  (dcw_dualBarrierGraph ω n).Reachable (rot90Fun a) (rot90Fun b) ↔ (pdc_barrierGraphPrimal ω n).Reachable a b := by
-- proof
  apply StatMech.Universality.pdc_dualReach_iff_primalReach ω n a b

/--
[pdc_DualCutConnectsRot_of_primalConnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_DualCutConnectsRot_of_primalConnects_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (h : pdc_PrimalBarrierConnects ω n) :
-- imply
  dcp_DualCutConnectsRot ω n := by
-- proof
  apply StatMech.Universality.pdc_DualCutConnectsRot_of_primalConnects ω n h

/--
[pdc_rotatedDualVerticalCrossing_of_primalConnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_rotatedDualVerticalCrossing_of_primalConnects_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (h : pdc_PrimalBarrierConnects ω n) :
-- imply
  DualVerticalCrossing ω (-n) 0 0 n := by
-- proof
  apply StatMech.Universality.pdc_rotatedDualVerticalCrossing_of_primalConnects ω n h

/--
[pdc_bottomBarrierEdge_primal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_bottomBarrierEdge_primal_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  ∃ v w : Site 2, (pdc_barrierGraphPrimal ω n).Adj v w ∧ v 1 = 0 ∧ w 1 = 0 := by
-- proof
  apply StatMech.Universality.pdc_bottomBarrierEdge_primal ω n hn hnoH

/--
[pdc_topBarrierEdge_primal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_topBarrierEdge_primal_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  ∃ v w : Site 2, (pdc_barrierGraphPrimal ω n).Adj v w ∧ v 1 = n ∧ w 1 = n := by
-- proof
  apply StatMech.Universality.pdc_topBarrierEdge_primal ω n hn hnoH

/--
[pdc_primalBarrier_nonempty_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_primalBarrier_nonempty_edge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  ∃ a b : Site 2, (pdc_barrierGraphPrimal ω n).Adj a b := by
-- proof
  apply StatMech.Universality.pdc_primalBarrier_nonempty_edge ω n hn hnoH

/--
[pdc_dualWalk_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_dualWalk_endpoints_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {a b : Site 2}
-- given
  (ha : a ∈ leftSide 0 n 0 n)
  (hb : b ∈ rightSide 0 n 0 n) :
-- imply
  rot90Fun a ∈ bottomSide (-n) 0 0 n ∧ rot90Fun b ∈ topSide (-n) 0 0 n := by
-- proof
  apply StatMech.Universality.pdc_dualWalk_endpoints ω n ha hb

/--
[pdc_rot90Inv_bottomSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_rot90Inv_bottomSide_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
  {p : Site 2}
-- given
  (hp : p ∈ bottomSide (-n) 0 0 n) :
-- imply
  rot90Inv p ∈ leftSide 0 n 0 n := by
-- proof
  apply StatMech.Universality.pdc_rot90Inv_bottomSide n hp

/--
[pdc_rot90Inv_topSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_rot90Inv_topSide_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
  {q : Site 2}
-- given
  (hq : q ∈ topSide (-n) 0 0 n) :
-- imply
  rot90Inv q ∈ rightSide 0 n 0 n := by
-- proof
  apply StatMech.Universality.pdc_rot90Inv_topSide n hq

/--
[pdc_primalConnects_of_DualCutConnectsRot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_primalConnects_of_DualCutConnectsRot_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (h : dcp_DualCutConnectsRot ω n) :
-- imply
  pdc_PrimalBarrierConnects ω n := by
-- proof
  apply StatMech.Universality.pdc_primalConnects_of_DualCutConnectsRot ω n h

/--
[pdc_primalConnects_iff_DualCutConnectsRot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_primalConnects_iff_DualCutConnectsRot_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  pdc_PrimalBarrierConnects ω n ↔ dcp_DualCutConnectsRot ω n := by
-- proof
  apply StatMech.Universality.pdc_primalConnects_iff_DualCutConnectsRot ω n

/--
[pdc_share_at_inside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_share_at_inside_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v w₁ w₂ : Site 2}
-- given
  (hbar₁ : dcw_isBarrierEdge ω n v w₁)
  (hbar₂ : dcw_isBarrierEdge ω n v w₂) :
-- imply
  (pdc_barrierGraphPrimal ω n).Reachable w₁ w₂ := by
-- proof
  apply StatMech.Universality.pdc_share_at_inside ω n hbar₁ hbar₂

/--
[pdc_share_at_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_share_at_outside_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v₁ v₂ w : Site 2}
-- given
  (hbar₁ : dcw_isBarrierEdge ω n v₁ w)
  (hbar₂ : dcw_isBarrierEdge ω n v₂ w) :
-- imply
  (pdc_barrierGraphPrimal ω n).Reachable v₁ v₂ := by
-- proof
  apply StatMech.Universality.pdc_share_at_outside ω n hbar₁ hbar₂

/--
[pdc_barrierEdge_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_barrierEdge_reachable_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v w : Site 2}
-- given
  (hbar : dcw_isBarrierEdge ω n v w) :
-- imply
  (pdc_barrierGraphPrimal ω n).Reachable v w := by
-- proof
  apply StatMech.Universality.pdc_barrierEdge_reachable ω n hbar

/--
[pdc_allClosed_leftReach_x0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_allClosed_leftReach_x0_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
  {v : Site 2}
-- given
  (hv : v ∈ bcd_leftReach (fun _ => false) n) :
-- imply
  v 0 = 0 := by
-- proof
  apply StatMech.Universality.pdc_allClosed_leftReach_x0 n hv

/--
[pdc_allClosed_noH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_allClosed_noH_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ¬ HorizontalCrossing (fun _ => false) 0 n 0 n := by
-- proof
  apply StatMech.Universality.pdc_allClosed_noH n hn

/--
[pdc_allClosed_rightSide_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_allClosed_rightSide_isolated_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
  {b : Site 2}
  {z : Site 2}
-- given
  (hn : 2 ≤ n)
  (hb : b ∈ rightSide 0 n 0 n) :
-- imply
  ¬ (pdc_barrierGraphPrimal (fun _ => false) n).Adj b z := by
-- proof
  apply StatMech.Universality.pdc_allClosed_rightSide_isolated n hn hb z

/--
[pdc_allClosed_not_primalConnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_allClosed_not_primalConnects_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
-- given
  (hn : 2 ≤ n) :
-- imply
  ¬ pdc_PrimalBarrierConnects (fun _ => false) n := by
-- proof
  apply StatMech.Universality.pdc_allClosed_not_primalConnects n hn

/--
[pdc_allClosed_not_DualCutConnectsRot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean)
-/
@[path]
private lemma pdc_allClosed_not_DualCutConnectsRot_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
-- given
  (hn : 2 ≤ n) :
-- imply
  ¬ dcp_DualCutConnectsRot (fun _ => false) n := by
-- proof
  apply StatMech.Universality.pdc_allClosed_not_DualCutConnectsRot n hn


-- created on 2026-10-23
