import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationLib
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[jsl_interiorConnected_of_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_interiorConnected_of_covers_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {sIn : Site 2}
-- given
  (hoff : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
  (hcov : jec_leftRegion Vc ⊆ offSupportComponent Vc sIn) :
-- imply
  jsl_InteriorConnected Vc := by
-- proof
  apply StatMech.Lattice.jsl_interiorConnected_of_covers Vc hoff hcov

/--
[jsl_outside_connected_of_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_outside_connected_of_reachesExterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hFlood : oc_OutsideReachesExterior Vc R) :
-- imply
  ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.jsl_outside_connected_of_reachesExterior Vc R hsupp hFlood

/--
[jsl_offComplComponentCount_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_offComplComponentCount_eq_two_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support)
  (hyout : y ∉ jec_leftRegion Vc)
  (hyoff : y ∉ Vc.support)
  (hin : jsl_InteriorConnected Vc)
  (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jsl_offComplComponentCount_eq_two Vc hxin hxoff hyout hyoff hin hout

/--
[jsl_offComplComponentCount_eq_two_of_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_offComplComponentCount_eq_two_of_floodFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support)
  (hyout : y ∉ jec_leftRegion Vc)
  (hyoff : y ∉ Vc.support)
  (hin : jsl_InteriorConnected Vc)
  (hFlood : oc_OutsideReachesExterior Vc R) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jsl_offComplComponentCount_eq_two_of_floodFill Vc R hsupp hxin hxoff hyout hyoff hin hFlood

/--
[jsl_offComplComponentCount_eq_faceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_offComplComponentCount_eq_faceCount_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
  {x y : Site 2}
-- given
  (hc : c.IsCycle)
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support)
  (hyout : y ∉ jec_leftRegion Vc)
  (hyoff : y ∉ Vc.support)
  (hin : jsl_InteriorConnected Vc)
  (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = faceCount c.toSubgraph.coe := by
-- proof
  apply StatMech.Lattice.jsl_offComplComponentCount_eq_faceCount Vc c hc hxin hxoff hyout hyoff hin hout

/--
[jsl_offComplComponentCount_eq_faceCount_of_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_offComplComponentCount_eq_faceCount_of_floodFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
  {x y : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hc : c.IsCycle)
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support)
  (hyout : y ∉ jec_leftRegion Vc)
  (hyoff : y ∉ Vc.support)
  (hin : jsl_InteriorConnected Vc)
  (hFlood : oc_OutsideReachesExterior Vc R) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = faceCount c.toSubgraph.coe := by
-- proof
  apply StatMech.Lattice.jsl_offComplComponentCount_eq_faceCount_of_floodFill Vc R hsupp c hc hxin hxoff hyout hyoff hin hFlood

/--
[jsl_fcb_eq_icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_fcb_eq_icc_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  fcb_offComplGraph Vc = icc_offComplGraph Vc := by
-- proof
  apply StatMech.Lattice.jsl_fcb_eq_icc Vc

/--
[jsl_iccCount_of_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_iccCount_of_floodFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support)
  (hyout : y ∉ jec_leftRegion Vc)
  (hyoff : y ∉ Vc.support)
  (hin : jsl_InteriorConnected Vc)
  (hFlood : oc_OutsideReachesExterior Vc R) :
-- imply
  Nat.card (icc_offComplGraph Vc).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jsl_iccCount_of_floodFill Vc R hsupp hxin hxoff hyout hyoff hin hFlood

/--
[jsl_interiorCovers_of_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_interiorCovers_of_floodFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {sIn sOut : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hInMem : sIn ∈ jec_leftRegion Vc)
  (hInOff : sIn ∉ Vc.support)
  (hOutMem : sOut ∉ jec_leftRegion Vc)
  (hOutOff : sOut ∉ Vc.support)
  (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
  (hin : jsl_InteriorConnected Vc)
  (hFlood : oc_OutsideReachesExterior Vc R) :
-- imply
  jec_leftRegion Vc ⊆ offSupportComponent Vc sIn := by
-- proof
  apply StatMech.Lattice.jsl_interiorCovers_of_floodFill Vc R hsupp hInMem hInOff hOutMem hOutOff hoffIn hin hFlood

/--
[jsl_two_components_of_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_two_components_of_floodFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {p q : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
  (hoffOut : ∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support)
  (hin : jsl_InteriorConnected Vc)
  (hFlood : oc_OutsideReachesExterior Vc R) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jsl_two_components_of_floodFill Vc R hsupp hp hq hoffIn hoffOut hin hFlood

/--
[jsl_peierls_long_range_order_of_planarConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_peierls_long_range_order_of_planarConnectivity_eq
  {a : Site 2}
-- given
  (hConn : ∀ n : ℕ, Ising.PlanarConnectivity n) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → Ising.plusMeasure 2 n β 0 ≠ Ising.minusMeasure 2 n β 0 := by
-- proof
  apply StatMech.Lattice.jsl_peierls_long_range_order_of_planarConnectivity hConn

/--
[jsl_components_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_components_distinct_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support)
  (hyout : y ∉ jec_leftRegion Vc)
  (hyoff : y ∉ Vc.support) :
-- imply
  (fcb_offComplGraph Vc).connectedComponentMk ⟨x, hxoff⟩ ≠ (fcb_offComplGraph Vc).connectedComponentMk ⟨y, hyoff⟩ := by
-- proof
  apply StatMech.Lattice.jsl_components_distinct Vc hxin hxoff hyout hyoff

/--
[jsl_count_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_count_ge_two_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  [Empty.Finite (fcb_offComplGraph Vc).ConnectedComponent]
  {x y : Site 2}
-- given
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support)
  (hyout : y ∉ jec_leftRegion Vc)
  (hyoff : y ∉ Vc.support) :
-- imply
  2 ≤ Nat.card (fcb_offComplGraph Vc).ConnectedComponent := by
-- proof
  apply StatMech.Lattice.jsl_count_ge_two Vc hxin hxoff hyout hyoff

/--
[jsl_minimalLoop_offComplComponentCount_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_minimalLoop_offComplComponentCount_eq_two_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hsupp : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R)
  (hxin : x ∈ jec_leftRegion (mpl_orbitLoop K a))
  (hxoff : x ∉ (mpl_orbitLoop K a).support)
  (hyout : y ∉ jec_leftRegion (mpl_orbitLoop K a))
  (hyoff : y ∉ (mpl_orbitLoop K a).support)
  (hin : jsl_InteriorConnected (mpl_orbitLoop K a))
  (hFlood : oc_OutsideReachesExterior (mpl_orbitLoop K a) R) :
-- imply
  Nat.card (fcb_offComplGraph (mpl_orbitLoop K a)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jsl_minimalLoop_offComplComponentCount_eq_two K a R hsupp hxin hxoff hyout hyoff hin hFlood

/--
[jsl_minimalLoop_interiorCovers_of_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_minimalLoop_interiorCovers_of_floodFill_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {sIn sOut : Site 2}
-- given
  (hsupp : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R)
  (hInMem : sIn ∈ jec_leftRegion (mpl_orbitLoop K a))
  (hInOff : sIn ∉ (mpl_orbitLoop K a).support)
  (hOutMem : sOut ∉ jec_leftRegion (mpl_orbitLoop K a))
  (hOutOff : sOut ∉ (mpl_orbitLoop K a).support)
  (hoffIn : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
  (hin : jsl_InteriorConnected (mpl_orbitLoop K a))
  (hFlood : oc_OutsideReachesExterior (mpl_orbitLoop K a) R) :
-- imply
  jec_leftRegion (mpl_orbitLoop K a) ⊆ offSupportComponent (mpl_orbitLoop K a) sIn := by
-- proof
  apply StatMech.Lattice.jsl_minimalLoop_interiorCovers_of_floodFill K a R hsupp hInMem hInOff hOutMem hOutOff hoffIn hin hFlood

/--
[jsl_minimalLoop_two_components_of_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_minimalLoop_two_components_of_floodFill_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {p q : Site 2}
-- given
  (hsupp : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R)
  (hp : ¬ Even (jec_rayCount p (mpl_orbitLoop K a)))
  (hq : ∀ w ∈ (mpl_orbitLoop K a).support, w 0 ≤ q 0 - 1)
  (hoffIn : ∀ s ∈ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
  (hoffOut : ∀ s ∉ jec_leftRegion (mpl_orbitLoop K a), s ∉ (mpl_orbitLoop K a).support)
  (hin : jsl_InteriorConnected (mpl_orbitLoop K a))
  (hFlood : oc_OutsideReachesExterior (mpl_orbitLoop K a) R) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion (mpl_orbitLoop K a))).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jsl_minimalLoop_two_components_of_floodFill K a R hsupp hp hq hoffIn hoffOut hin hFlood

/--
[jsl_floodFill_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_floodFill_nonvacuous_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hz : z ∈ exterior 2 R) :
-- imply
  ∃ e : Site 2, e ∈ exterior 2 R ∧ (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
-- proof
  apply StatMech.Lattice.jsl_floodFill_nonvacuous Vc R hz

/--
[jsl_exterior_hub_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_exterior_hub_nonvacuous_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hx : x ∈ exterior 2 R)
  (hy : y ∈ exterior 2 R) :
-- imply
  (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y := by
-- proof
  apply StatMech.Lattice.jsl_exterior_hub_nonvacuous Vc R hsupp hx hy

/--
[jsl_offComplComponentCount_eq_two_of_reachesTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_offComplComponentCount_eq_two_of_reachesTop_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support)
  (hyout : y ∉ jec_leftRegion Vc)
  (hyoff : y ∉ Vc.support)
  (hin : jsl_InteriorConnected Vc)
  (hTop : oc_OutsideReachesTop Vc R) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jsl_offComplComponentCount_eq_two_of_reachesTop Vc R hsupp hxin hxoff hyout hyoff hin hTop

/--
[jsl_two_components_of_reachesTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean)
-/
@[path]
private lemma jsl_two_components_of_reachesTop_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {p q : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
  (hoffOut : ∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support)
  (hin : jsl_InteriorConnected Vc)
  (hTop : oc_OutsideReachesTop Vc R) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jsl_two_components_of_reachesTop Vc R hsupp hp hq hoffIn hoffOut hin hTop


-- created on 2026-10-23
