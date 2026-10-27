import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Walls.wlrleftring.Part3
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[wlr_leftBoundary_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean)
-/
@[path]
private lemma wlr_leftBoundary_off_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {w : Site 2}
-- given
  (hw : w ∈ wic_leftBoundary Vc) :
-- imply
  w ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.wlr_leftBoundary_off Vc hw

/--
[wlr_leftBoundary_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean)
-/
@[path]
private lemma wlr_leftBoundary_interior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {w : Site 2}
-- given
  (hw : w ∈ wic_leftBoundary Vc) :
-- imply
  w ∈ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.wlr_leftBoundary_interior Vc hw

/--
[wlr_leftBoundary_westSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean)
-/
@[path]
private lemma wlr_leftBoundary_westSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {w : Site 2}
-- given
  (hw : w ∈ wic_leftBoundary Vc) :
-- imply
  (![w 0 - 1, w 1] : Site 2) ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.wlr_leftBoundary_westSupport Vc hw

/--
[wlr_horizAdj_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean)
-/
@[path]
private lemma wlr_horizAdj_reachable_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c r : ℤ}
-- given
  (h0 : (![c, r] : Site 2) ∉ Vc.support)
  (h1 : (![c + 1, r] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable (![c, r] : Site 2) (![c + 1, r] : Site 2) := by
-- proof
  apply StatMech.Lattice.wlr_horizAdj_reachable Vc h0 h1

/--
[wlr_vertAdj_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean)
-/
@[path]
private lemma wlr_vertAdj_reachable_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c r : ℤ}
-- given
  (h0 : (![c, r] : Site 2) ∉ Vc.support)
  (h1 : (![c, r + 1] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable (![c, r] : Site 2) (![c, r + 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.wlr_vertAdj_reachable Vc h0 h1

/--
[wlr_adjacent_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean)
-/
@[path]
private lemma wlr_adjacent_reachable_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ Vc.support)
  (hv : v ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable u v := by
-- proof
  apply StatMech.Lattice.wlr_adjacent_reachable Vc hadj hu hv

/--
[wlr_vertWall_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean)
-/
@[path]
private lemma wlr_vertWall_reachable_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c r0 r1 : ℤ}
-- given
  (hoff : ∀ t : ℤ, t ∈ Set.uIcc r0 r1 → (![c, t] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable (![c, r0] : Site 2) (![c, r1] : Site 2) := by
-- proof
  apply StatMech.Lattice.wlr_vertWall_reachable Vc c r0 r1 hoff

/--
[wlr_horizRun_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean)
-/
@[path]
private lemma wlr_horizRun_reachable_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {r x0 x1 : ℤ}
-- given
  (hoff : ∀ t : ℤ, t ∈ Set.uIcc x0 x1 → (![t, r] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable (![x0, r] : Site 2) (![x1, r] : Site 2) := by
-- proof
  apply StatMech.Lattice.wlr_horizRun_reachable Vc r x0 x1 hoff

/--
[wlr_leftBoundary_subset_innerRing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean)
-/
@[path]
private lemma wlr_leftBoundary_subset_innerRing_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  wic_leftBoundary Vc ⊆ wlr_innerRing Vc := by
-- proof
  apply StatMech.Lattice.wlr_leftBoundary_subset_innerRing Vc

/--
[wlr_leftBoundaryConnected_of_innerRingConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean)
-/
@[path]
private lemma wlr_leftBoundaryConnected_of_innerRingConnected_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wlr_InnerRingConnected Vc) :
-- imply
  wic_LeftBoundaryConnected Vc := by
-- proof
  apply StatMech.Lattice.wlr_leftBoundaryConnected_of_innerRingConnected Vc h

/--
[wlr_winding_separation_of_innerRing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean)
-/
@[path]
private lemma wlr_winding_separation_of_innerRing_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {sIn : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hsInmem : sIn ∈ jec_leftRegion Vc)
  (hsInoff : sIn ∉ Vc.support)
  (hres : wlr_InnerRingConnected Vc)
  (hNoBddEven : woc_NoBoundedEvenComponent Vc) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.wlr_winding_separation_of_innerRing Vc R hsupp hsInmem hsInoff hres hNoBddEven

/--
[wlr_support_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean)
-/
@[path]
private lemma wlr_support_connected_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hu : u ∈ Vc.support)
  (hv : v ∈ Vc.support) :
-- imply
  ∃ p : (hypercubicLattice 2).Walk u v, ∀ z ∈ p.support, z ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.wlr_support_connected Vc hu hv


-- created on 2026-10-23
