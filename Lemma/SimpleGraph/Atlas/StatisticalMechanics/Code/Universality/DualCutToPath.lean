import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.DualCutToPath.Part4
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[dcp_barrier_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_barrier_separates_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x y : Site 2}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hx : x ∈ leftSide 0 n 0 n)
  (hy : y ∈ rightSide 0 n 0 n) :
-- imply
  ¬ (latticeMinusBarrier (bcd_leftReach ω n)).Reachable x y := by
-- proof
  apply StatMech.Universality.dcp_barrier_separates ω n hnoH hx hy

/--
[dcp_topBarrierEdge_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_topBarrierEdge_exists_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  ∃ v w : Site 2, dcw_isBarrierEdge ω n v w ∧ v 1 = n ∧ w 1 = n := by
-- proof
  apply StatMech.Universality.dcp_topBarrierEdge_exists ω n hn hnoH

/--
[dcp_dualBarrierGraph_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_dualBarrierGraph_support_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {p q : Site 2}
-- given
  (h : (dcw_dualBarrierGraph ω n).Adj p q) :
-- imply
  p ∈ rot90Fun '' (rect 0 n 0 n) ∧ q ∈ rot90Fun '' (rect 0 n 0 n) := by
-- proof
  apply StatMech.Universality.dcp_dualBarrierGraph_support ω n h

/--
[dcp_dualBarrierGraph_finite_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_dualBarrierGraph_finite_support_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  {p : Site 2 | ∃ q, (dcw_dualBarrierGraph ω n).Adj p q}.Finite := by
-- proof
  apply StatMech.Universality.dcp_dualBarrierGraph_finite_support ω n

/--
[dcp_route_of_cutConnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_route_of_cutConnects_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hcut : dcp_DualCutConnects ω n) :
-- imply
  dcw_BarrierRoute ω n := by
-- proof
  apply StatMech.Universality.dcp_route_of_cutConnects ω n hcut

/--
[dcp_dualVerticalCrossing_of_cutConnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_dualVerticalCrossing_of_cutConnects_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hcut : dcp_DualCutConnects ω n) :
-- imply
  DualVerticalCrossing ω 0 n 0 n := by
-- proof
  apply StatMech.Universality.dcp_dualVerticalCrossing_of_cutConnects ω n hcut

/--
[dcp_dichotomy_of_cutConnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_dichotomy_of_cutConnects_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
-- given
  (hcut : ∀ ω : ConfigSpace (Sym2 (Site 2)), ¬ HorizontalCrossing ω 0 n 0 n → dcp_DualCutConnects ω n) :
-- imply
  (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n := by
-- proof
  apply StatMech.Universality.dcp_dichotomy_of_cutConnects n hcut

/--
[dcp_bottomBarrierVertex_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_bottomBarrierVertex_exists_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  ∃ v : Site 2, v 1 = 0 ∧ (∃ q, (dcw_dualBarrierGraph ω n).Adj (rot90Fun v) q) := by
-- proof
  apply StatMech.Universality.dcp_bottomBarrierVertex_exists ω n hn hnoH

/--
[dcp_topBarrierVertex_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_topBarrierVertex_exists_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  ∃ v : Site 2, v 1 = n ∧ (∃ q, (dcw_dualBarrierGraph ω n).Adj (rot90Fun v) q) := by
-- proof
  apply StatMech.Universality.dcp_topBarrierVertex_exists ω n hn hnoH

/--
[dcp_rot90_bottomRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_rot90_bottomRow_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {a : ℤ} :
-- imply
  rot90Fun ![a, 0] = ![0, a] := by
-- proof
  apply StatMech.Universality.dcp_rot90_bottomRow a

/--
[dcp_rot90_topRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_rot90_topRow_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {a n : ℤ} :
-- imply
  rot90Fun ![a, n] = ![-n, a] := by
-- proof
  apply StatMech.Universality.dcp_rot90_topRow a n

/--
[dcp_cutReachable_of_cutConnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_cutReachable_of_cutConnects_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hcut : dcp_DualCutConnects ω n) :
-- imply
  dcp_CutReachable ω n := by
-- proof
  apply StatMech.Universality.dcp_cutReachable_of_cutConnects ω n hcut

/--
[dcp_dualOpen_reachable_of_cutConnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_dualOpen_reachable_of_cutConnects_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hcut : dcp_DualCutConnects ω n) :
-- imply
  ∃ (p₀ : Site 2) (_hp₀ : p₀ ∈ bottomSide 0 n 0 n) (q₀ : Site 2) (_hq₀ : q₀ ∈ topSide 0 n 0 n), (openSubgraph 2 (dualConfig ω)).Reachable p₀ q₀ := by
-- proof
  apply StatMech.Universality.dcp_dualOpen_reachable_of_cutConnects ω n hcut

/--
[dcp_dualBarrierGraph_support_rot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_dualBarrierGraph_support_rot_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {p q : Site 2}
-- given
  (h : (dcw_dualBarrierGraph ω n).Adj p q) :
-- imply
  p ∈ rect (-n) 0 0 n := by
-- proof
  apply StatMech.Universality.dcp_dualBarrierGraph_support_rot ω n h

/--
[dcp_rot90_leftSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_rot90_leftSide_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
  {x : Site 2}
-- given
  (hx : x ∈ leftSide 0 n 0 n) :
-- imply
  rot90Fun x ∈ bottomSide (-n) 0 0 n := by
-- proof
  apply StatMech.Universality.dcp_rot90_leftSide n hx

/--
[dcp_rot90_rightSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_rot90_rightSide_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
  {x : Site 2}
-- given
  (hx : x ∈ rightSide 0 n 0 n) :
-- imply
  rot90Fun x ∈ topSide (-n) 0 0 n := by
-- proof
  apply StatMech.Universality.dcp_rot90_rightSide n hx

/--
[dcp_barrierWalk_support_rot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_barrierWalk_support_rot_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {p q : Site 2}
  {c : (dcw_dualBarrierGraph ω n).Walk p q}
-- given
  (hp : p ∈ rect (-n) 0 0 n) :
-- imply
  ∀ u ∈ c.support, u ∈ rect (-n) 0 0 n := by
-- proof
  apply StatMech.Universality.dcp_barrierWalk_support_rot ω n c hp

/--
[dcp_rotatedDualVerticalCrossing_of_cutConnectsRot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_rotatedDualVerticalCrossing_of_cutConnectsRot_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hcut : dcp_DualCutConnectsRot ω n) :
-- imply
  DualVerticalCrossing ω (-n) 0 0 n := by
-- proof
  apply StatMech.Universality.dcp_rotatedDualVerticalCrossing_of_cutConnectsRot ω n hcut

/--
[dcp_rotatedCut_nonempty_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean)
-/
@[path]
private lemma dcp_rotatedCut_nonempty_edge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  ∃ p q : Site 2, (dcw_dualBarrierGraph ω n).Adj p q ∧ p ∈ rect (-n) 0 0 n ∧ q ∈ rect (-n) 0 0 n := by
-- proof
  apply StatMech.Universality.dcp_rotatedCut_nonempty_edge ω n hn hnoH


-- created on 2026-10-23
