import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection
open Finset StatMech StatMech.FrontierD StatMech.FrontierD.IntegralSquareTorusCycle


/--
[xFlux_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma xFlux_pred_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {x : ZMod L} :
-- imply
  C.xFlux x = C.xFlux (x - 1) := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.xFlux_pred C x

/--
[yFlux_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma yFlux_pred_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {y : ZMod L} :
-- imply
  C.yFlux y = C.yFlux (y - 1) := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.yFlux_pred C y

/--
[xFlux_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma xFlux_eq_neg_one_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {x : ZMod L} :
-- imply
  C.xFlux x = C.xFlux (-1) := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.xFlux_eq_neg_one C x

/--
[yFlux_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma yFlux_eq_neg_one_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {y : ZMod L} :
-- imply
  C.yFlux y = C.yFlux (-1) := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.yFlux_eq_neg_one C y

/--
[zeroFlux_divergence_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma zeroFlux_divergence_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : ZMod L × ZMod L} :
-- imply
  C.zeroFluxHorizontal p + C.zeroFluxVertical p - C.zeroFluxHorizontal (p.1 - 1, p.2) - C.zeroFluxVertical (p.1, p.2 - 1) = 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.zeroFlux_divergence_zero C p

/--
[zeroFluxHorizontal_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma zeroFluxHorizontal_sum_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {x : ZMod L} :
-- imply
  ∑ y : ZMod L, C.zeroFluxHorizontal (x, y) = 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.zeroFluxHorizontal_sum_zero C x

/--
[zeroFluxVertical_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma zeroFluxVertical_sum_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {y : ZMod L} :
-- imply
  ∑ x : ZMod L, C.zeroFluxVertical (x, y) = 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.zeroFluxVertical_sum_zero C y

/--
[zmodPrefix_sub_pred_of_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma zmodPrefix_sub_pred_of_sum_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {f : ZMod L → Int}
  {z : ZMod L}
-- given
  (hsum : ∑ z, f z = 0) :
-- imply
  ons_zmodPrefix f z - ons_zmodPrefix f (z - 1) = f z := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.zmodPrefix_sub_pred_of_sum_zero f hsum z

/--
[streamPotential_vertical_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma streamPotential_vertical_boundary_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : ZMod L × ZMod L} :
-- imply
  C.streamPotential (p.1 - 1, p.2) - C.streamPotential p = C.zeroFluxVertical p := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.streamPotential_vertical_boundary C p

/--
[streamPotential_horizontal_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma streamPotential_horizontal_boundary_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : ZMod L × ZMod L} :
-- imply
  C.streamPotential p - C.streamPotential (p.1, p.2 - 1) = C.zeroFluxHorizontal p := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.streamPotential_horizontal_boundary C p

/--
[zeroFlux_intersection_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma zeroFlux_intersection_eq_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {C D : IntegralSquareTorusCycle L} :
-- imply
  ∑ p : ZMod L × ZMod L, (C.zeroFluxHorizontal p * D.vertical (p.1, p.2 - 1) - C.zeroFluxVertical p * D.horizontal (p.1 - 1, p.2)) = 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.zeroFlux_intersection_eq_zero C D

/--
[intersection_eq_flux_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma intersection_eq_flux_det_eq
  {L : Nat}
  [Fact (2 < L)]
  {C D : IntegralSquareTorusCycle L} :
-- imply
  C.intersection D = C.xFlux (-1) * D.yFlux (-1) - C.yFlux (-1) * D.xFlux (-1) := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.intersection_eq_flux_det C D

/--
[intersection_eq_zero_of_locallyDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma intersection_eq_zero_of_locallyDisjoint_eq
  {L : Nat}
  [Fact (2 < L)]
  {C D : IntegralSquareTorusCycle L}
-- given
  (h : C.LocallyDisjoint D) :
-- imply
  C.intersection D = 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.intersection_eq_zero_of_locallyDisjoint h

/--
[flux_det_eq_zero_of_locallyDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma flux_det_eq_zero_of_locallyDisjoint_eq
  {L : Nat}
  [Fact (2 < L)]
  {C D : IntegralSquareTorusCycle L}
-- given
  (h : C.LocallyDisjoint D) :
-- imply
  C.xFlux (-1) * D.yFlux (-1) - C.yFlux (-1) * D.xFlux (-1) = 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.flux_det_eq_zero_of_locallyDisjoint h

/--
[pointMass_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma pointMass_west_eq
  {L : Nat}
  [Fact (2 < L)]
  {a p : ZMod L × ZMod L} :
-- imply
  pointMass a (p.1 - 1, p.2) = pointMass (a.1 + 1, a.2) p := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.pointMass_west a p

/--
[pointMass_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma pointMass_south_eq
  {L : Nat}
  [Fact (2 < L)]
  {a p : ZMod L × ZMod L} :
-- imply
  pointMass a (p.1, p.2 - 1) = pointMass (a.1, a.2 + 1) p := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.pointMass_south a p

/--
[dart_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma dart_divergence_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {p : ZMod L × ZMod L} :
-- imply
  dartHorizontal d p + dartVertical d p - dartHorizontal d (p.1 - 1, p.2) - dartVertical d (p.1, p.2 - 1) = pointMass d.1 p - pointMass (ons_dirStep L d.2 d.1) p := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.dart_divergence d p

/--
[dartHorizontal_xSeam_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma dartHorizontal_xSeam_sum_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : ons_Dart L} :
-- imply
  (∑ y : ZMod L, dartHorizontal d (-1, y)) = ons_xWrapSign d := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.dartHorizontal_xSeam_sum d

/--
[dartVertical_ySeam_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma dartVertical_ySeam_sum_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : ons_Dart L} :
-- imply
  (∑ x : ZMod L, dartVertical d (x, -1)) = ons_yWrapSign d := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.dartVertical_ySeam_sum d

/--
[ofDarts_xFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma ofDarts_xFlux_eq
  {L : Nat}
  [Fact (2 < L)]
  {n : Nat}
  [NeZero n]
  {v : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
-- imply
  (ofDarts v hvalid).xFlux (-1) = ∑ k, ons_xWrapSign (v k) := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.ofDarts_xFlux v hvalid

/--
[ofDarts_yFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma ofDarts_yFlux_eq
  {L : Nat}
  [Fact (2 < L)]
  {n : Nat}
  [NeZero n]
  {v : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
-- imply
  (ofDarts v hvalid).yFlux (-1) = ∑ k, ons_yWrapSign (v k) := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.ofDarts_yFlux v hvalid

/--
[dartLoop_winding_det_eq_zero_of_locallyDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma dartLoop_winding_det_eq_zero_of_locallyDisjoint_eq
  {L : Nat}
  [Fact (2 < L)]
  {n m : Nat}
  [NeZero n]
  [NeZero m]
  {v : Fin n → ons_Dart L}
  {w : Fin m → ons_Dart L}
-- given
  (hv : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hw : ∀ k : Fin m, (w k).1 = ons_dirStep L (w (k + 1)).2 (w (k + 1)).1)
  (hdisj : (ofDarts v hv).LocallyDisjoint (ofDarts w hw)) :
-- imply
  (∑ k, ons_xWrapSign (v k)) * (∑ k, ons_yWrapSign (w k)) - (∑ k, ons_yWrapSign (v k)) * (∑ k, ons_xWrapSign (w k)) = 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.dartLoop_winding_det_eq_zero_of_locallyDisjoint v hv w hw hdisj

/--
[ofDartList_xFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma ofDartList_xFlux_eq
  {L : Nat}
  [Fact (2 < L)]
  {l : List (ons_Dart L)}
-- given
  (hbalanced : DartListBalanced l) :
-- imply
  (ofDartList l hbalanced).xFlux (-1) = (l.map ons_xWrapSign).sum := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.ofDartList_xFlux l hbalanced

/--
[ofDartList_yFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma ofDartList_yFlux_eq
  {L : Nat}
  [Fact (2 < L)]
  {l : List (ons_Dart L)}
-- given
  (hbalanced : DartListBalanced l) :
-- imply
  (ofDartList l hbalanced).yFlux (-1) = (l.map ons_yWrapSign).sum := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.ofDartList_yFlux l hbalanced

/--
[dartList_winding_det_eq_zero_of_locallyDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusIntersection.lean)
-/
@[path]
private lemma dartList_winding_det_eq_zero_of_locallyDisjoint_eq
  {L : Nat}
  [Fact (2 < L)]
  {v : List (ons_Dart L)}
  {w : List (ons_Dart L)}
-- given
  (hv : DartListBalanced v)
  (hw : DartListBalanced w)
  (hdisj : (ofDartList v hv).LocallyDisjoint (ofDartList w hw)) :
-- imply
  (v.map ons_xWrapSign).sum * (w.map ons_yWrapSign).sum - (v.map ons_yWrapSign).sum * (w.map ons_xWrapSign).sum = 0 := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.dartList_winding_det_eq_zero_of_locallyDisjoint v hv w hw hdisj


-- created on 2026-10-23
