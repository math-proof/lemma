import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kc10core
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc10_collar_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean)
-/
@[path]
private lemma kc10_collar_up_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hzoff : z ∉ Vc.support)
  (hupOff : (![z 0, z 1 + 1] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable z ![z 0, z 1 + 1] := by
-- proof
  apply StatMech.Walls.kc10_collar_up Vc hzoff hupOff

/--
[kc10_support_row_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean)
-/
@[path]
private lemma kc10_support_row_le_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {s : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hs : s ∈ Vc.support) :
-- imply
  s 1 ≤ (R : ℤ) := by
-- proof
  apply StatMech.Walls.kc10_support_row_le Vc R hsupp hs

/--
[kc10_rightNb_offSupport_of_highRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean)
-/
@[path]
private lemma kc10_rightNb_offSupport_of_highRow_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hrow : (R : ℤ) < z 1) :
-- imply
  (![z 0 + 1, z 1] : Site 2) ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc10_rightNb_offSupport_of_highRow Vc R hsupp hrow

/--
[kc10_rightStep_of_collarSlide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean)
-/
@[path]
private lemma kc10_rightStep_of_collarSlide_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hslide : kc10_CollarSlide Vc R) :
-- imply
  ecc_RightStep Vc R := by
-- proof
  apply StatMech.Walls.kc10_rightStep_of_collarSlide Vc R hsupp hslide

/--
[kc10_rightDodge_of_collarSlide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean)
-/
@[path]
private lemma kc10_rightDodge_of_collarSlide_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hslide : kc10_CollarSlide Vc R) :
-- imply
  ecc_RightDodge Vc R := by
-- proof
  apply StatMech.Walls.kc10_rightDodge_of_collarSlide Vc R hsupp hslide

/--
[kc10_rightNb_offSupport_of_lowRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean)
-/
@[path]
private lemma kc10_rightNb_offSupport_of_lowRow_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hrow : z 1 < -(R : ℤ)) :
-- imply
  (![z 0 + 1, z 1] : Site 2) ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc10_rightNb_offSupport_of_lowRow Vc R hsupp hrow

/--
[kc10_rightStep_of_collarSlideDown](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean)
-/
@[path]
private lemma kc10_rightStep_of_collarSlideDown_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hslide : kc10_CollarSlideDown Vc R) :
-- imply
  ecc_RightStep Vc R := by
-- proof
  apply StatMech.Walls.kc10_rightStep_of_collarSlideDown Vc R hsupp hslide

/--
[kc10_rightDodge_of_collarSlideDown](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean)
-/
@[path]
private lemma kc10_rightDodge_of_collarSlideDown_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hslide : kc10_CollarSlideDown Vc R) :
-- imply
  ecc_RightDodge Vc R := by
-- proof
  apply StatMech.Walls.kc10_rightDodge_of_collarSlideDown Vc R hsupp hslide

/--
[kc10_collarSlide_of_offSupportReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean)
-/
@[path]
private lemma kc10_collarSlide_of_offSupportReaches_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hesc : kc5_OffSupportReachesExterior Vc R) :
-- imply
  kc10_CollarSlide Vc R := by
-- proof
  apply StatMech.Walls.kc10_collarSlide_of_offSupportReaches Vc R hsupp hesc

/--
[kc10_collarSlideDown_of_offSupportReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean)
-/
@[path]
private lemma kc10_collarSlideDown_of_offSupportReaches_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hesc : kc5_OffSupportReachesExterior Vc R) :
-- imply
  kc10_CollarSlideDown Vc R := by
-- proof
  apply StatMech.Walls.kc10_collarSlideDown_of_offSupportReaches Vc R hsupp hesc

/--
[kc10_unitCell_collarSlide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean)
-/
@[path]
private lemma kc10_unitCell_collarSlide_eq
  {a : Site 2} :
-- imply
  kc10_CollarSlide (mpl_orbitLoop unitCell ucBase) 1 := by
-- proof
  apply StatMech.Walls.kc10_unitCell_collarSlide

/--
[kc10_unitCell_rightDodge_via_collarSlide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean)
-/
@[path]
private lemma kc10_unitCell_rightDodge_via_collarSlide_eq
  {a : Site 2} :
-- imply
  ecc_RightDodge (mpl_orbitLoop unitCell ucBase) 1 := by
-- proof
  apply StatMech.Walls.kc10_unitCell_rightDodge_via_collarSlide

/--
[kc10_unitCell_collarSlideDown](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean)
-/
@[path]
private lemma kc10_unitCell_collarSlideDown_eq
  {a : Site 2} :
-- imply
  kc10_CollarSlideDown (mpl_orbitLoop unitCell ucBase) 1 := by
-- proof
  apply StatMech.Walls.kc10_unitCell_collarSlideDown

/--
[kc10_offSupportReaches_of_collarSlide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean)
-/
@[path]
private lemma kc10_offSupportReaches_of_collarSlide_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : oc_supportSet Vc ⊆ box 2 R)
  (hslide : kc10_CollarSlide Vc R) :
-- imply
  kc5_OffSupportReachesExterior Vc R := by
-- proof
  apply StatMech.Walls.kc10_offSupportReaches_of_collarSlide Vc R hsupp hslide

/--
[kc10_offSupportOutsideInfinite_of_collarSlide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean)
-/
@[path]
private lemma kc10_offSupportOutsideInfinite_of_collarSlide_eq
  {a : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hbridge : kc6_OffSupportOutsideInK K a)
  (hslide : kc10_CollarSlide (mpl_orbitLoop K a) R) :
-- imply
  kc7_OffSupportOutsideInfinite K a := by
-- proof
  apply StatMech.Walls.kc10_offSupportOutsideInfinite_of_collarSlide K a R hRbox hbridge hslide


-- created on 2026-10-23
