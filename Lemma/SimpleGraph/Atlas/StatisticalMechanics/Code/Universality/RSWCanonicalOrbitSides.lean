import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWCanonicalOrbitSides
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_dartFace_step_sharedPrimalEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_dartFace_step_sharedPrimalEdge_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  sharedPrimalEdge (dartFace e) (dartFace (dartNext K e)) = s(e.tail, e.head) := by
-- proof
  apply StatMech.Universality.rlc_dartFace_step_sharedPrimalEdge K e

/--
[rlc_dartFace_step_eq_flankFaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_dartFace_step_eq_flankFaces_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  s(dartFace e, dartFace (dartNext K e)) = flankFaces e.tail e.head := by
-- proof
  apply StatMech.Universality.rlc_dartFace_step_eq_flankFaces K e he

/--
[rlc_dartFace_step_injective_on_boundaryDarts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_dartFace_step_injective_on_boundaryDarts_eq
  {K : Set (Site 2)}
  {e f : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hf : IsBoundaryDart K f)
  (hstep : s(dartFace e, dartFace (dartNext K e)) = s(dartFace f, dartFace (dartNext K f))) :
-- imply
  e = f := by
-- proof
  apply StatMech.Universality.rlc_dartFace_step_injective_on_boundaryDarts K he hf hstep

/--
[rlc_mpl_orbitFaceLoop_isTrail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_mpl_orbitFaceLoop_isTrail_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (mpl_orbitFaceLoop K a).IsTrail := by
-- proof
  apply StatMech.Universality.rlc_mpl_orbitFaceLoop_isTrail K a

/--
[rlc_mpl_orbitLoop_base_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_mpl_orbitLoop_base_bdEdge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  bdEdge (jec_leftRegion (mpl_orbitLoop K a)) s(a.1.tail, a.1.head) := by
-- proof
  apply StatMech.Universality.rlc_mpl_orbitLoop_base_bdEdge K hK a

/--
[rlc_orbitLoop_sameSide_of_sameSide_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_orbitLoop_sameSide_of_sameSide_K_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hsame : (u ∈ K ↔ v ∈ K)) :
-- imply
  (u ∈ jec_leftRegion (mpl_orbitLoop K a) ↔ v ∈ jec_leftRegion (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Universality.rlc_orbitLoop_sameSide_of_sameSide_K K a hadj hsame

/--
[rlc_orbitLoop_const_on_barrierComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_orbitLoop_const_on_barrierComponent_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {u v : Site 2}
-- given
  (hreach : (latticeMinusBarrier K).Reachable u v) :
-- imply
  (u ∈ jec_leftRegion (mpl_orbitLoop K a) ↔ v ∈ jec_leftRegion (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Universality.rlc_orbitLoop_const_on_barrierComponent K a hreach

/--
[rlc_mpl_orbitLoop_contains_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_mpl_orbitLoop_contains_of_connected_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hhead : a.1.head ∉ jec_leftRegion (mpl_orbitLoop K a))
  (hconn : ∀ z ∈ K, (latticeMinusBarrier K).Reachable a.1.tail z) :
-- imply
  K ⊆ jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Universality.rlc_mpl_orbitLoop_contains_of_connected K hK a hhead hconn

/--
[rlc_mpl_orbitLoop_excludes_of_head_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_mpl_orbitLoop_excludes_of_head_reachable_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hhead : a.1.head ∉ jec_leftRegion (mpl_orbitLoop K a))
  (hz : (latticeMinusBarrier K).Reachable a.1.head z) :
-- imply
  z ∉ jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Universality.rlc_mpl_orbitLoop_excludes_of_head_reachable K a hhead hz

/--
[rlc_faceBoundary_support_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_faceBoundary_support_lower_bound_eq
  {K : Set (Site 2)}
  {R : ℕ}
  {f : Site 2}
-- given
  (hbox : K ⊆ box 2 R)
  (hf : f ∈ (faceBoundaryGraph K).support) :
-- imply
  -((R : ℤ)) - 1 ≤ f 0 := by
-- proof
  apply StatMech.Universality.rlc_faceBoundary_support_lower_bound K R hbox hf

/--
[rlc_mpl_orbitLoop_head_outside_of_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_mpl_orbitLoop_head_outside_of_box_eq
  {K : Set (Site 2)}
  {R : ℕ}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hbox : K ⊆ box 2 R)
  (hheadExt : a.1.head ∈ exterior 2 R) :
-- imply
  a.1.head ∉ jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Universality.rlc_mpl_orbitLoop_head_outside_of_box K hK R hbox a hheadExt

/--
[rlc_latticeOn_reachable_of_walk_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_latticeOn_reachable_of_walk_support_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hsupp : ∀ z ∈ w.support, z ∈ S) :
-- imply
  (Ising.latticeOn S).Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_latticeOn_reachable_of_walk_support S w hsupp

/--
[rlc_mixedWiredReachSet_latticeOn_reachable_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_latticeOn_reachable_lower_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_mixedWiredReachSet G omega) :
-- imply
  (Ising.latticeOn (rlc_mixedWiredReachSet G omega)).Reachable G.lowerVertex z := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_latticeOn_reachable_lower G omega hz

/--
[rlc_mixedWiredReachSet_subset_natBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_subset_natBox_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n) :
-- imply
  rlc_mixedWiredReachSet G omega ⊆ box 2 (2 * n).toNat := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_subset_natBox G hn omega

/--
[rlc_outerExitDart_head_mem_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_outerExitDart_head_mem_exterior_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n) :
-- imply
  (rlc_outerExitDart G omega).head ∈ exterior 2 (2 * n).toNat := by
-- proof
  apply StatMech.Universality.rlc_outerExitDart_head_mem_exterior G hn omega

/--
[rlc_outerExitAnchor_head_not_mem_windingRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_outerExitAnchor_head_not_mem_windingRegion_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n) :
-- imply
  (rlc_outerExitAnchor G omega).1.head ∉ rlc_outerExitWindingRegion G omega := by
-- proof
  apply StatMech.Universality.rlc_outerExitAnchor_head_not_mem_windingRegion G hn omega

/--
[rlc_mixedWiredReachSet_subset_outerExitWindingRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_mixedWiredReachSet_subset_outerExitWindingRegion_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n) :
-- imply
  rlc_mixedWiredReachSet G omega ⊆ rlc_outerExitWindingRegion G omega := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredReachSet_subset_outerExitWindingRegion G hn omega

/--
[rlc_latticeOn_compl_reachable_of_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_latticeOn_compl_reachable_of_exterior_eq
  {K : Set (Site 2)}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hbox : K ⊆ box 2 R)
  (hx : x ∈ exterior 2 R)
  (hy : y ∈ exterior 2 R) :
-- imply
  (Ising.latticeOn Kᶜ).Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_latticeOn_compl_reachable_of_exterior K R hbox hx hy

/--
[rlc_leftPathVertex_reachable_leftStart_in_compl_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_leftPathVertex_reachable_leftStart_in_compl_of_failure_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {z : Site 2}
-- given
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
  (hz : z ∈ rlc_pathVertices gamma'.1) :
-- imply
  (Ising.latticeOn (rlc_mixedWiredReachSet G omega)ᶜ).Reachable z (gamma'.1.1 : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_leftPathVertex_reachable_leftStart_in_compl_of_failure G omega hno hz

/--
[rlc_outerExitHead_reachable_leftPathVertex_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_outerExitHead_reachable_leftPathVertex_of_failure_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {z : Site 2}
-- given
  (hn : 0 < n)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
  (hz : z ∈ rlc_pathVertices gamma'.1) :
-- imply
  (Ising.latticeOn (rlc_mixedWiredReachSet G omega)ᶜ).Reachable (rlc_outerExitAnchor G omega).1.head z := by
-- proof
  apply StatMech.Universality.rlc_outerExitHead_reachable_leftPathVertex_of_failure G hn omega hno hz

/--
[rlc_outerExitJordanTraceSides_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_outerExitJordanTraceSides_of_failure_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
-- imply
  RlcOuterExitJordanTraceSides G omega := by
-- proof
  apply StatMech.Universality.rlc_outerExitJordanTraceSides_of_failure G hn omega hno

/--
[rlc_outerExitTraceSeparation_of_failure_of_preimageSplit_closedJordan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_outerExitTraceSeparation_of_failure_of_preimageSplit_closedJordan_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
  (htrace : RlcLowestHighestTracePreimageSplit gamma gamma') :
-- imply
  RlcOuterExitTraceSeparation G hn hlt omega := by
-- proof
  apply StatMech.Universality.rlc_outerExitTraceSeparation_of_failure_of_preimageSplit_closedJordan G hn hlt omega hno htrace

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_failure_closedJordan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWCanonicalOrbitSides.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_failure_closedJordan_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
  (htrace : RlcLowestHighestTracePreimageSplit gamma gamma')
  (horder : RlcOuterExitContactArcOrder G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_failure_closedJordan G hn hlt omega hno htrace horder


-- created on 2026-10-23
