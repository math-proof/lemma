import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.wicinterior.Part3
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[wic_eta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wicinterior.lean)
-/
@[path]
private lemma wic_eta_eq
  {a : Site 2}
  {w : Site 2} :
-- imply
  (![w 0, w 1] : Site 2) = w := by
-- proof
  apply StatMech.Lattice.wic_eta w

/--
[wic_marchLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wicinterior.lean)
-/
@[path]
private lemma wic_marchLeft_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hz : z ∈ jec_leftRegion Vc)
  (hzoff : z ∉ Vc.support) :
-- imply
  ∃ c₀ : ℤ, c₀ ≤ z 0 ∧ (offSupport Vc).Reachable z (![c₀, z 1] : Site 2) ∧ (![c₀, z 1] : Site 2) ∈ jec_leftRegion Vc ∧ (![c₀, z 1] : Site 2) ∉ Vc.support ∧ (![c₀ - 1, z 1] : Site 2) ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.wic_marchLeft Vc R hsupp hz hzoff

/--
[wic_reaches_leftBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wicinterior.lean)
-/
@[path]
private lemma wic_reaches_leftBoundary_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hz : z ∈ jec_leftRegion Vc)
  (hzoff : z ∉ Vc.support) :
-- imply
  ∃ w ∈ wic_leftBoundary Vc, (offSupport Vc).Reachable z w := by
-- proof
  apply StatMech.Lattice.wic_reaches_leftBoundary Vc R hsupp hz hzoff

/--
[wic_interiorConnected_of_leftBoundaryConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wicinterior.lean)
-/
@[path]
private lemma wic_interiorConnected_of_leftBoundaryConnected_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {sIn : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hsInmem : sIn ∈ jec_leftRegion Vc)
  (hsInoff : sIn ∉ Vc.support)
  (hLB : ∀ u v : Site 2, u ∈ wic_leftBoundary Vc → v ∈ wic_leftBoundary Vc → (offSupport Vc).Reachable u v) :
-- imply
  wch_InteriorConnected Vc := by
-- proof
  apply StatMech.Lattice.wic_interiorConnected_of_leftBoundaryConnected Vc R hsupp hsInmem hsInoff hLB

/--
[wic_interiorConnected_of_hubReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wicinterior.lean)
-/
@[path]
private lemma wic_interiorConnected_of_hubReaches_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {hub : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hhubmem : hub ∈ jec_leftRegion Vc)
  (hhuboff : hub ∉ Vc.support)
  (hhub : ∀ w ∈ wic_leftBoundary Vc, (offSupport Vc).Reachable hub w) :
-- imply
  wch_InteriorConnected Vc := by
-- proof
  apply StatMech.Lattice.wic_interiorConnected_of_hubReaches Vc R hsupp hhubmem hhuboff hhub

/--
[wic_interiorConnected_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wicinterior.lean)
-/
@[path]
private lemma wic_interiorConnected_of_residue_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {sIn : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hsInmem : sIn ∈ jec_leftRegion Vc)
  (hsInoff : sIn ∉ Vc.support)
  (hres : wic_LeftBoundaryConnected Vc) :
-- imply
  wch_InteriorConnected Vc := by
-- proof
  apply StatMech.Lattice.wic_interiorConnected_of_residue Vc R hsupp hsInmem hsInoff hres

/--
[wic_winding_separation_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wicinterior.lean)
-/
@[path]
private lemma wic_winding_separation_of_residue_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {sIn : Site 2}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hsInmem : sIn ∈ jec_leftRegion Vc)
  (hsInoff : sIn ∉ Vc.support)
  (hres : wic_LeftBoundaryConnected Vc)
  (hNoBddEven : woc_NoBoundedEvenComponent Vc) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.wic_winding_separation_of_residue Vc R hsupp hsInmem hsInoff hres hNoBddEven


-- created on 2026-10-23
