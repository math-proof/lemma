import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc_core
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc_backwardHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_backwardHalf_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hflip : u ∈ jec_leftRegion Vc ↔ v ∉ jec_leftRegion Vc) :
-- imply
  bdEdge (jec_leftRegion Vc) s(u, v) := by
-- proof
  apply StatMech.Walls.kc_backwardHalf Vc hflip

/--
[kc_windingBoundary_iff_support_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_windingBoundary_iff_support_flip_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  bdEdge (jec_leftRegion Vc) s(u, v) ↔ ((u ∈ jec_leftRegion Vc ↔ v ∉ jec_leftRegion Vc) ∧ (u ∈ Vc.support ∨ v ∈ Vc.support)) := by
-- proof
  apply StatMech.Walls.kc_windingBoundary_iff_support_flip Vc hadj

/--
[kc_leftRegion_eq_of_rayParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_leftRegion_eq_of_rayParity_eq
  {K : Set (Site 2)}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z Vc))
  (hout : ∀ z, z ∉ K → Even (jec_rayCount z Vc)) :
-- imply
  K = jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc_leftRegion_eq_of_rayParity Vc hin hout

/--
[kc_bdEdgeMatch_of_rayParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_bdEdgeMatch_of_rayParity_eq
  {K : Set (Site 2)}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z Vc))
  (hout : ∀ z, z ∉ K → Even (jec_rayCount z Vc)) :
-- imply
  pww_BdEdgeMatch K Vc := by
-- proof
  apply StatMech.Walls.kc_bdEdgeMatch_of_rayParity Vc hin hout

/--
[kc_exteriorEven_iff_interiorSubset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_exteriorEven_iff_interiorSubset_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  eaw_InteriorSubset K a ↔ (∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a))) := by
-- proof
  apply StatMech.Walls.kc_exteriorEven_iff_interiorSubset K a

/--
[kc_exteriorEven_of_interiorSubset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_exteriorEven_of_interiorSubset_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hint : eaw_InteriorSubset K a) :
-- imply
  ∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.kc_exteriorEven_of_interiorSubset K a hint

/--
[kc_rayParity_in_of_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_rayParity_in_of_windingWitness_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hw : wei_WindingWitness K a)
  (hInt : ∀ z₀, z₀ ∈ K → ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z₀, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)) :
-- imply
  ∀ z, z ∈ K → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.kc_rayParity_in_of_windingWitness K a hw hInt

/--
[kc_core_of_interiorSubset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_core_of_interiorSubset_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hw : wei_WindingWitness K a)
  (hInt : ∀ z₀, z₀ ∈ K → ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z₀, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support))
  (hint : eaw_InteriorSubset K a) :
-- imply
  pww_BdEdgeMatch K (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.kc_core_of_interiorSubset K a hw hInt hint

/--
[kc_core_leftRegion_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_core_leftRegion_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hw : wei_WindingWitness K a)
  (hInt : ∀ z₀, z₀ ∈ K → ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z₀, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support))
  (hint : eaw_InteriorSubset K a) :
-- imply
  K = jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.kc_core_leftRegion_eq K a hw hInt hint

/--
[kc_core_crossedEdge_backwardHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_core_crossedEdge_backwardHalf_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f g : Site 2}
-- given
  (hw : wei_WindingWitness K a)
  (hInt : ∀ z₀, z₀ ∈ K → ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z₀, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support))
  (hint : eaw_InteriorSubset K a)
  (hedge : s(f, g) ∈ (mpl_orbitLoop K a).edges) :
-- imply
  bdEdge (jec_leftRegion (mpl_orbitLoop K a)) (sharedPrimalEdge f g) := by
-- proof
  apply StatMech.Walls.kc_core_crossedEdge_backwardHalf K a hw hInt hint hedge

/--
[kc_core_leftFence_of_interiorSubset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_core_leftFence_of_interiorSubset_eq
  {K : Set (Site 2)}
  {z₀ : Site 2}
  {m : ℤ}
-- given
  (hK : K.Finite)
  (hbd : IsBoundaryDart K (lmo_leftDartAt z₀))
  (hm : z₀ 0 = m)
  (hmin : ∀ w ∈ K, m ≤ w 0)
  (hcyc : (mpl_orbitLoop K ⟨lmo_leftDartAt z₀, hbd⟩).IsCycle)
  (hInt : ∀ z₀', z₀' ∈ K → ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z₀', (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K ⟨lmo_leftDartAt z₀, hbd⟩).support))
  (hint : eaw_InteriorSubset K ⟨lmo_leftDartAt z₀, hbd⟩) :
-- imply
  pww_BdEdgeMatch K (mpl_orbitLoop K ⟨lmo_leftDartAt z₀, hbd⟩) := by
-- proof
  apply StatMech.Walls.kc_core_leftFence_of_interiorSubset K hK z₀ hbd m hm hmin hcyc hInt hint

/--
[kc_core_starHull_of_interiorSubset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_core_starHull_of_interiorSubset_eq
  {K : Set (Site 2)}
  {z₀ : Site 2}
  {m : ℤ}
-- given
  (hK : K.Finite)
  (hbd : IsBoundaryDart (ndt_StarHull K) (lmo_leftDartAt z₀))
  (hm : z₀ 0 = m)
  (hmin : ∀ w ∈ ndt_StarHull K, m ≤ w 0)
  (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) ⟨lmo_leftDartAt z₀, hbd⟩)
  (hInt : ∀ z₀', z₀' ∈ ndt_StarHull K → ∀ z, z ∈ ndt_StarHull K → ∃ p : (hypercubicLattice 2).Walk z z₀', (∀ w ∈ p.support, w ∉ (mpl_orbitLoop (ndt_StarHull K) ⟨lmo_leftDartAt z₀, hbd⟩).support))
  (hint : eaw_InteriorSubset (ndt_StarHull K) ⟨lmo_leftDartAt z₀, hbd⟩) :
-- imply
  pww_BdEdgeMatch (ndt_StarHull K) (mpl_orbitLoop (ndt_StarHull K) ⟨lmo_leftDartAt z₀, hbd⟩) := by
-- proof
  apply StatMech.Walls.kc_core_starHull_of_interiorSubset K hK z₀ hbd m hm hmin hp hInt hint

/--
[kc_core_of_exc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_core_of_exc_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hw : wei_WindingWitness K a)
  (hInt : ∀ z₀, z₀ ∈ K → ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z₀, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support))
  (hoff : exc_OffSupportReachesExterior K a)
  (hsupp : exc_SupportOddInK K a) :
-- imply
  pww_BdEdgeMatch K (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.kc_core_of_exc K a hw hInt hoff hsupp

/--
[kc_core_leftFence_of_exc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_core_leftFence_of_exc_eq
  {K : Set (Site 2)}
  {z₀ : Site 2}
  {m : ℤ}
-- given
  (hK : K.Finite)
  (hbd : IsBoundaryDart K (lmo_leftDartAt z₀))
  (hm : z₀ 0 = m)
  (hmin : ∀ w ∈ K, m ≤ w 0)
  (hcyc : (mpl_orbitLoop K ⟨lmo_leftDartAt z₀, hbd⟩).IsCycle)
  (hInt : ∀ z₀', z₀' ∈ K → ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z₀', (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K ⟨lmo_leftDartAt z₀, hbd⟩).support))
  (hoff : exc_OffSupportReachesExterior K ⟨lmo_leftDartAt z₀, hbd⟩)
  (hsupp : exc_SupportOddInK K ⟨lmo_leftDartAt z₀, hbd⟩) :
-- imply
  pww_BdEdgeMatch K (mpl_orbitLoop K ⟨lmo_leftDartAt z₀, hbd⟩) := by
-- proof
  apply StatMech.Walls.kc_core_leftFence_of_exc K hK z₀ hbd m hm hmin hcyc hInt hoff hsupp

/--
[kc_unitCell_supportOddInK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_unitCell_supportOddInK_eq :
-- imply
  exc_SupportOddInK unitCell ucBase := by
-- proof
  apply StatMech.Walls.kc_unitCell_supportOddInK

/--
[kc_unitCell_interiorSubset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_unitCell_interiorSubset_eq :
-- imply
  eaw_InteriorSubset unitCell ucBase := by
-- proof
  apply StatMech.Walls.kc_unitCell_interiorSubset

/--
[kc_unitCell_exteriorEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_core.lean)
-/
@[path]
private lemma kc_unitCell_exteriorEven_eq :
-- imply
  ∀ z, z ∉ unitCell → Even (jec_rayCount z (mpl_orbitLoop unitCell ucBase)) := by
-- proof
  apply StatMech.Walls.kc_unitCell_exteriorEven


-- created on 2026-10-23
