import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc3_core
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc3_leftRegion_eq_of_bdEdgeMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_leftRegion_eq_of_bdEdgeMatch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hmatch : pww_BdEdgeMatch K (mpl_orbitLoop K a)) :
-- imply
  K = jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.kc3_leftRegion_eq_of_bdEdgeMatch K hK a hmatch

/--
[kc3_downFaceEven_of_leftRegion_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_downFaceEven_of_leftRegion_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hKeq : K = jec_leftRegion (mpl_orbitLoop K a)) :
-- imply
  kc2_DownFaceEven K a := by
-- proof
  apply StatMech.Walls.kc3_downFaceEven_of_leftRegion_eq K a hKeq

/--
[kc3_upFaceInK_of_leftRegion_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_upFaceInK_of_leftRegion_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hKeq : K = jec_leftRegion (mpl_orbitLoop K a)) :
-- imply
  kc2_UpFaceInK K a := by
-- proof
  apply StatMech.Walls.kc3_upFaceInK_of_leftRegion_eq K a hKeq

/--
[kc3_leftFaceInK_of_leftRegion_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_leftFaceInK_of_leftRegion_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hKeq : K = jec_leftRegion (mpl_orbitLoop K a)) :
-- imply
  kc2_LeftFaceInK K a := by
-- proof
  apply StatMech.Walls.kc3_leftFaceInK_of_leftRegion_eq K a hKeq

/--
[kc3_three_of_leftRegion_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_three_of_leftRegion_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hKeq : K = jec_leftRegion (mpl_orbitLoop K a)) :
-- imply
  kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a := by
-- proof
  apply StatMech.Walls.kc3_three_of_leftRegion_eq K a hKeq

/--
[kc3_core_of_leftRegion_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_core_of_leftRegion_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hKeq : K = jec_leftRegion (mpl_orbitLoop K a)) :
-- imply
  exc_SupportOddInK K a := by
-- proof
  apply StatMech.Walls.kc3_core_of_leftRegion_eq K a hKeq

/--
[kc3_three_of_bdEdgeMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_three_of_bdEdgeMatch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hmatch : pww_BdEdgeMatch K (mpl_orbitLoop K a)) :
-- imply
  kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a := by
-- proof
  apply StatMech.Walls.kc3_three_of_bdEdgeMatch K hK a hmatch

/--
[kc3_core_of_bdEdgeMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_core_of_bdEdgeMatch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hmatch : pww_BdEdgeMatch K (mpl_orbitLoop K a)) :
-- imply
  exc_SupportOddInK K a := by
-- proof
  apply StatMech.Walls.kc3_core_of_bdEdgeMatch K hK a hmatch

/--
[kc3_core_of_bdEdgeMatch_via_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_core_of_bdEdgeMatch_via_three_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hmatch : pww_BdEdgeMatch K (mpl_orbitLoop K a)) :
-- imply
  exc_SupportOddInK K a := by
-- proof
  apply StatMech.Walls.kc3_core_of_bdEdgeMatch_via_three K hK a hmatch

/--
[kc3_leftRegion_eq_of_bridge_halves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_leftRegion_eq_of_bridge_halves_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)))
  (hout : ∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a))) :
-- imply
  K = jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.kc3_leftRegion_eq_of_bridge_halves K a hin hout

/--
[kc3_core_of_bridge_halves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_core_of_bridge_halves_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)))
  (hout : ∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a))) :
-- imply
  exc_SupportOddInK K a := by
-- proof
  apply StatMech.Walls.kc3_core_of_bridge_halves K a hin hout

/--
[kc3_three_of_bridge_halves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_three_of_bridge_halves_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)))
  (hout : ∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a))) :
-- imply
  kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a := by
-- proof
  apply StatMech.Walls.kc3_three_of_bridge_halves K a hin hout

/--
[kc3_interiorSubset_of_bdEdgeMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_interiorSubset_of_bdEdgeMatch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hmatch : pww_BdEdgeMatch K (mpl_orbitLoop K a))
  (hoff : exc_OffSupportReachesExterior K a) :
-- imply
  eaw_InteriorSubset K a := by
-- proof
  apply StatMech.Walls.kc3_interiorSubset_of_bdEdgeMatch K hK a hmatch hoff

/--
[kc3_interiorSubset_of_bridge_halves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_interiorSubset_of_bridge_halves_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)))
  (hout : ∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a)))
  (hoff : exc_OffSupportReachesExterior K a) :
-- imply
  eaw_InteriorSubset K a := by
-- proof
  apply StatMech.Walls.kc3_interiorSubset_of_bridge_halves K a hin hout hoff

/--
[kc3_unitCell_leftRegion_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_unitCell_leftRegion_eq_eq :
-- imply
  unitCell = jec_leftRegion (mpl_orbitLoop unitCell ucBase) := by
-- proof
  apply StatMech.Walls.kc3_unitCell_leftRegion_eq

/--
[kc3_unitCell_bdEdgeMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_unitCell_bdEdgeMatch_eq :
-- imply
  pww_BdEdgeMatch unitCell (mpl_orbitLoop unitCell ucBase) := by
-- proof
  apply StatMech.Walls.kc3_unitCell_bdEdgeMatch

/--
[kc3_unitCell_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_unitCell_three_eq :
-- imply
  kc2_DownFaceEven unitCell ucBase ∧ kc2_UpFaceInK unitCell ucBase ∧ kc2_LeftFaceInK unitCell ucBase := by
-- proof
  apply StatMech.Walls.kc3_unitCell_three

/--
[kc3_unitCell_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_unitCell_core_eq :
-- imply
  exc_SupportOddInK unitCell ucBase := by
-- proof
  apply StatMech.Walls.kc3_unitCell_core

/--
[kc3_leftRegion_eq_iff_bdEdgeMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_leftRegion_eq_iff_bdEdgeMatch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  K = jec_leftRegion (mpl_orbitLoop K a) ↔ pww_BdEdgeMatch K (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.kc3_leftRegion_eq_iff_bdEdgeMatch K hK a

/--
[kc3_core_of_bdEdgeMatch_summary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_core.lean)
-/
@[path]
private lemma kc3_core_of_bdEdgeMatch_summary_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hmatch : pww_BdEdgeMatch K (mpl_orbitLoop K a)) :
-- imply
  (kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a) ∧ exc_SupportOddInK K a := by
-- proof
  apply StatMech.Walls.kc3_core_of_bdEdgeMatch_summary K hK a hmatch


-- created on 2026-10-23
