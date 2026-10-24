import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kc6core
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc6_interiorSubset_of_halves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6core.lean)
-/
@[path]
private lemma kc6_interiorSubset_of_halves_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hoff : exc_OffSupportReachesExterior K a)
  (hsupp : exc_SupportOddInK K a) :
-- imply
  eaw_InteriorSubset K a := by
-- proof
  apply StatMech.Walls.kc6_interiorSubset_of_halves K a hoff hsupp

/--
[kc6_leftRegion_subset_of_halves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6core.lean)
-/
@[path]
private lemma kc6_leftRegion_subset_of_halves_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hoff : exc_OffSupportReachesExterior K a)
  (hsupp : exc_SupportOddInK K a) :
-- imply
  jec_leftRegion (mpl_orbitLoop K a) ⊆ K := by
-- proof
  apply StatMech.Walls.kc6_leftRegion_subset_of_halves K a hoff hsupp

/--
[kc6_offSupportReaches_of_noHoles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6core.lean)
-/
@[path]
private lemma kc6_offSupportReaches_of_noHoles_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hbridge : kc6_OffSupportOutsideInK K a)
  (hnoHoles : kc5_OutsideOffSupportInfinite (mpl_orbitLoop K a)) :
-- imply
  exc_OffSupportReachesExterior K a := by
-- proof
  apply StatMech.Walls.kc6_offSupportReaches_of_noHoles K a R hRbox hbridge hnoHoles

/--
[kc6_interiorSubset_of_supportOdd_and_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6core.lean)
-/
@[path]
private lemma kc6_interiorSubset_of_supportOdd_and_bridge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hsupp : exc_SupportOddInK K a)
  (hbridge : kc6_OffSupportOutsideInK K a) :
-- imply
  eaw_InteriorSubset K a := by
-- proof
  apply StatMech.Walls.kc6_interiorSubset_of_supportOdd_and_bridge K a hsupp hbridge

/--
[kc6_bridge_iff_offSupport_inside_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6core.lean)
-/
@[path]
private lemma kc6_bridge_iff_offSupport_inside_subset_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  kc6_OffSupportOutsideInK K a ↔ ∀ z, z ∉ (mpl_orbitLoop K a).support → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) → z ∈ K := by
-- proof
  apply StatMech.Walls.kc6_bridge_iff_offSupport_inside_subset K a

/--
[kc6_interiorSubset_of_supportOdd_and_noHoles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6core.lean)
-/
@[path]
private lemma kc6_interiorSubset_of_supportOdd_and_noHoles_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hsupp : exc_SupportOddInK K a)
  (hbridge : kc6_OffSupportOutsideInK K a)
  (hnoHoles : kc5_OutsideOffSupportInfinite (mpl_orbitLoop K a)) :
-- imply
  eaw_InteriorSubset K a := by
-- proof
  apply StatMech.Walls.kc6_interiorSubset_of_supportOdd_and_noHoles K a R hRbox hsupp hbridge hnoHoles

/--
[kc6_leftRegion_eq_of_core_and_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6core.lean)
-/
@[path]
private lemma kc6_leftRegion_eq_of_core_and_winding_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hcore : eaw_InteriorSubset K a)
  (hwind : K ⊆ jec_leftRegion (mpl_orbitLoop K a)) :
-- imply
  K = jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.kc6_leftRegion_eq_of_core_and_winding K a hcore hwind

/--
[kc6_bdEdgeMatch_of_core_and_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6core.lean)
-/
@[path]
private lemma kc6_bdEdgeMatch_of_core_and_winding_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hcore : eaw_InteriorSubset K a)
  (hwind : K ⊆ jec_leftRegion (mpl_orbitLoop K a)) :
-- imply
  pww_BdEdgeMatch K (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.kc6_bdEdgeMatch_of_core_and_winding K a hcore hwind

/--
[kc6_supportOddInK_iff_leftRegion_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6core.lean)
-/
@[path]
private lemma kc6_supportOddInK_iff_leftRegion_subset_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  exc_SupportOddInK K a ↔ kc3_LeftRegionSupportSubset K a := by
-- proof
  apply StatMech.Walls.kc6_supportOddInK_iff_leftRegion_subset K a

/--
[kc6_interiorSubset_of_setContainments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6core.lean)
-/
@[path]
private lemma kc6_interiorSubset_of_setContainments_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hsupp : kc3_LeftRegionSupportSubset K a)
  (hbridge : kc6_OffSupportOutsideInK K a)
  (hnoHoles : kc5_OutsideOffSupportInfinite (mpl_orbitLoop K a)) :
-- imply
  eaw_InteriorSubset K a := by
-- proof
  apply StatMech.Walls.kc6_interiorSubset_of_setContainments K a R hRbox hsupp hbridge hnoHoles

/--
[kc6_supportOdd_of_core_and_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6core.lean)
-/
@[path]
private lemma kc6_supportOdd_of_core_and_winding_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hcore : eaw_InteriorSubset K a)
  (hwind : K ⊆ jec_leftRegion (mpl_orbitLoop K a)) :
-- imply
  exc_SupportOddInK K a := by
-- proof
  apply StatMech.Walls.kc6_supportOdd_of_core_and_winding K hK a hcore hwind

/--
[kc6_unitCell_interiorSubset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6core.lean)
-/
@[path]
private lemma kc6_unitCell_interiorSubset_eq :
-- imply
  eaw_InteriorSubset unitCell ucBase := by
-- proof
  apply StatMech.Walls.kc6_unitCell_interiorSubset

/--
[kc6_unitCell_leftRegion_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6core.lean)
-/
@[path]
private lemma kc6_unitCell_leftRegion_eq_eq :
-- imply
  unitCell = jec_leftRegion (mpl_orbitLoop unitCell ucBase) := by
-- proof
  apply StatMech.Walls.kc6_unitCell_leftRegion_eq

/--
[kc6_unitCell_offSupportOutsideInK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6core.lean)
-/
@[path]
private lemma kc6_unitCell_offSupportOutsideInK_eq :
-- imply
  kc6_OffSupportOutsideInK unitCell ucBase := by
-- proof
  apply StatMech.Walls.kc6_unitCell_offSupportOutsideInK


-- created on 2026-10-23
