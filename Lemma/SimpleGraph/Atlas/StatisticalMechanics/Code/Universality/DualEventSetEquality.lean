import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[des_rot90Inv_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_rot90Inv_zero_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x : Site 2} :
-- imply
  (rot90Inv x) 0 = x 1 := by
-- proof
  apply StatMech.Universality.des_rot90Inv_zero x

/--
[des_rot90Inv_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_rot90Inv_one_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x : Site 2} :
-- imply
  (rot90Inv x) 1 = - x 0 := by
-- proof
  apply StatMech.Universality.des_rot90Inv_one x

/--
[des_rot90Inv_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_rot90Inv_rect_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rect 0 n 0 n ↔ rot90Inv x ∈ rect 0 n (-n) 0 := by
-- proof
  apply StatMech.Universality.des_rot90Inv_rect n x

/--
[des_rot90Inv_bottomSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_rot90Inv_bottomSide_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
  {x : Site 2} :
-- imply
  x ∈ bottomSide 0 n 0 n ↔ rot90Inv x ∈ leftSide 0 n (-n) 0 := by
-- proof
  apply StatMech.Universality.des_rot90Inv_bottomSide n x

/--
[des_rot90Inv_topSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_rot90Inv_topSide_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
  {x : Site 2} :
-- imply
  x ∈ topSide 0 n 0 n ↔ rot90Inv x ∈ rightSide 0 n (-n) 0 := by
-- proof
  apply StatMech.Universality.des_rot90Inv_topSide n x

/--
[des_negConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_negConfig_apply_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  des_negConfig ω e = !(ω e) := by
-- proof
  apply StatMech.Universality.des_negConfig_apply ω e

/--
[des_negConfig_open_iff_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_negConfig_open_iff_closed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  des_negConfig ω e = true ↔ ω e = false := by
-- proof
  apply StatMech.Universality.des_negConfig_open_iff_closed ω e

/--
[des_isOpenEdge_dual_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_isOpenEdge_dual_iff_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {p q : Site 2} :
-- imply
  IsOpenEdge 2 (dualConfig ω) p q ↔ IsOpenEdge 2 (des_negConfig ω) (rot90Inv p) (rot90Inv q) := by
-- proof
  apply StatMech.Universality.des_isOpenEdge_dual_iff ω p q

/--
[des_dualV_iff_negH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_dualV_iff_negH_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  DualVerticalCrossing ω 0 n 0 n ↔ HorizontalCrossing (des_negConfig ω) 0 n (-n) 0 := by
-- proof
  apply StatMech.Universality.des_dualV_iff_negH ω n

/--
[des_dualVerticalCrossingEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_dualVerticalCrossingEvent_eq_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ} :
-- imply
  dualVerticalCrossingEvent 0 n 0 n = {ω | HorizontalCrossing (des_negConfig ω) 0 n (-n) 0} := by
-- proof
  apply StatMech.Universality.des_dualVerticalCrossingEvent_eq n

/--
[des_hsepSquare_iff_closedH_rotbox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_hsepSquare_iff_closedH_rotbox_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ} :
-- imply
  ((horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) ↔ (∀ ω : ConfigSpace (Sym2 (Site 2)), ¬ HorizontalCrossing ω 0 n 0 n → HorizontalCrossing (des_negConfig ω) 0 n (-n) 0) := by
-- proof
  apply StatMech.Universality.des_hsepSquare_iff_closedH_rotbox n

/--
[des_cutConfig_cut_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_cutConfig_cut_closed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {b : ℤ} :
-- imply
  des_cutConfig s(![0, b], ![1, b]) = false := by
-- proof
  apply StatMech.Universality.des_cutConfig_cut_closed b

/--
[des_cutConfig_open_of_not_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_cutConfig_open_of_not_cut_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {e : Sym2 (Site 2)}
-- given
  (h : ¬ ∃ b : ℤ, e = s(![0, b], ![1, b])) :
-- imply
  des_cutConfig e = true := by
-- proof
  apply StatMech.Universality.des_cutConfig_open_of_not_cut h

/--
[des_cross_edge_is_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_cross_edge_is_cut_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u 0 = 0)
  (hv : v 0 = 1) :
-- imply
  s(u, v) = s(![0, u 1], ![1, u 1]) := by
-- proof
  apply StatMech.Universality.des_cross_edge_is_cut hadj hu hv

/--
[des_cutConfig_no_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_cutConfig_no_cross_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {u v : Site 2}
-- given
  (h : IsOpenEdge 2 des_cutConfig u v)
  (hu : u 0 = 0)
  (hv : v 0 = 1) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.des_cutConfig_no_cross h hu hv

/--
[des_cutConfig_open_sameSide0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_cutConfig_open_sameSide0_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {u v : Site 2}
-- given
  (h : IsOpenEdge 2 des_cutConfig u v) :
-- imply
  (u 0 ≤ 0 ↔ v 0 ≤ 0) := by
-- proof
  apply StatMech.Universality.des_cutConfig_open_sameSide0 h

/--
[des_cutConfig_connectedWithin_sameSide0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_cutConfig_connectedWithin_sameSide0_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {S : Set (Site 2)}
  {x y : S}
-- given
  (h : ConnectedWithin 2 des_cutConfig S x y) :
-- imply
  ((x : Site 2) 0 ≤ 0 ↔ (y : Site 2) 0 ≤ 0) := by
-- proof
  apply StatMech.Universality.des_cutConfig_connectedWithin_sameSide0 h

/--
[des_cutConfig_no_H](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_cutConfig_no_H_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ¬ HorizontalCrossing des_cutConfig 0 n 0 n := by
-- proof
  apply StatMech.Universality.des_cutConfig_no_H n hn

/--
[des_negCut_open_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_negCut_open_le_one_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {u v : Site 2}
-- given
  (h : IsOpenEdge 2 (des_negConfig des_cutConfig) u v) :
-- imply
  u 0 ≤ 1 ∧ v 0 ≤ 1 := by
-- proof
  apply StatMech.Universality.des_negCut_open_le_one h

/--
[des_negCut_connectedWithin_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_negCut_connectedWithin_le_one_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {S : Set (Site 2)}
  {x y : S}
-- given
  (h : ConnectedWithin 2 (des_negConfig des_cutConfig) S x y)
  (hx : (x : Site 2) 0 ≤ 1) :
-- imply
  (y : Site 2) 0 ≤ 1 := by
-- proof
  apply StatMech.Universality.des_negCut_connectedWithin_le_one h hx

/--
[des_cutConfig_no_negH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_cutConfig_no_negH_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
-- given
  (hn : 2 ≤ n) :
-- imply
  ¬ HorizontalCrossing (des_negConfig des_cutConfig) 0 n (-n) 0 := by
-- proof
  apply StatMech.Universality.des_cutConfig_no_negH n hn

/--
[des_hsepSquare_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean)
-/
@[path]
private lemma des_hsepSquare_false_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
-- given
  (hn : 2 ≤ n) :
-- imply
  ¬ ((horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.des_hsepSquare_false n hn


-- created on 2026-10-23
