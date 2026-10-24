import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.wchcovering
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[wch_bridge_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wchcovering.lean)
-/
@[path]
private lemma wch_bridge_false_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  ¬ wpj_PlaneDualityBridge Vc := by
-- proof
  apply StatMech.Lattice.wch_bridge_false Vc

/--
[wch_covers_off_pair_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wchcovering.lean)
-/
@[path]
private lemma wch_covers_off_pair_false_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {sIn sOut : Site 2}
-- given
  (hsInoff : sIn ∉ Vc.support)
  (hsOutoff : sOut ∉ Vc.support)
  (hcovIn : jec_leftRegion Vc ⊆ offSupportComponent Vc sIn)
  (hcovOut : (jec_leftRegion Vc)ᶜ ⊆ offSupportComponent Vc sOut) :
-- imply
  False := by
-- proof
  apply StatMech.Lattice.wch_covers_off_pair_false Vc hsInoff hsOutoff hcovIn hcovOut

/--
[wch_offComplJordanRegion_of_corrected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wchcovering.lean)
-/
@[path]
private lemma wch_offComplJordanRegion_of_corrected_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wch_CorrectedBridge Vc) :
-- imply
  fcb_OffComplJordanRegion Vc := by
-- proof
  apply StatMech.Lattice.wch_offComplJordanRegion_of_corrected Vc h

/--
[wch_winding_separation_of_corrected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wchcovering.lean)
-/
@[path]
private lemma wch_winding_separation_of_corrected_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wch_CorrectedBridge Vc) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.wch_winding_separation_of_corrected Vc h

/--
[wch_exteriorCovering_of_noBoundedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wchcovering.lean)
-/
@[path]
private lemma wch_exteriorCovering_of_noBoundedEven_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (h : woc_NoBoundedEvenComponent Vc) :
-- imply
  (beacon 2 R) ∉ jec_leftRegion Vc ∧ (beacon 2 R) ∉ Vc.support ∧ wch_ExteriorCovering Vc (beacon 2 R) := by
-- proof
  apply StatMech.Lattice.wch_exteriorCovering_of_noBoundedEven Vc R hsupp h

/--
[wch_winding_separation_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wchcovering.lean)
-/
@[path]
private lemma wch_winding_separation_of_residues_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hIntConn : wch_InteriorConnected Vc)
  (hNoBddEven : woc_NoBoundedEvenComponent Vc) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.wch_winding_separation_of_residues Vc R hsupp hIntConn hNoBddEven

/--
[wch_interiorConnected_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wchcovering.lean)
-/
@[path]
private lemma wch_interiorConnected_iff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {sIn : Site 2}
-- given
  (hsInmem : sIn ∈ jec_leftRegion Vc)
  (hsInoff : sIn ∉ Vc.support) :
-- imply
  wch_InteriorConnected Vc ↔ ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → (offSupport Vc).Reachable s t := by
-- proof
  apply StatMech.Lattice.wch_interiorConnected_iff Vc hsInmem hsInoff


-- created on 2026-10-23
