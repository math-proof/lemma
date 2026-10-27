import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicPhase.Part6
open StatMech StatMech.FrontierA


/--
[triangularPathDisplacement_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathDisplacement_nil_eq :
-- imply
  triangularPathDisplacement [] = 0 := by
-- proof
  apply StatMech.FrontierA.triangularPathDisplacement_nil

/--
[triangularPathDisplacement_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathDisplacement_cons_eq
  {d : Fin 6}
  {ds : List (Fin 6)} :
-- imply
  triangularPathDisplacement (d :: ds) = triangularIntStep d + triangularPathDisplacement ds := by
-- proof
  apply StatMech.FrontierA.triangularPathDisplacement_cons d ds

/--
[triangularPathVertices_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathVertices_nil_eq :
-- imply
  triangularPathVertices [] = [0] := by
-- proof
  apply StatMech.FrontierA.triangularPathVertices_nil

/--
[triangularPathVertices_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathVertices_cons_eq
  {d : Fin 6}
  {ds : List (Fin 6)} :
-- imply
  triangularPathVertices (d :: ds) = 0 :: (triangularPathVertices ds).map (triangularIntStep d + ·) := by
-- proof
  apply StatMech.FrontierA.triangularPathVertices_cons d ds

/--
[triangularPathDisplacement_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathDisplacement_append_eq
  {l r : List (Fin 6)} :
-- imply
  triangularPathDisplacement (l ++ r) = triangularPathDisplacement l + triangularPathDisplacement r := by
-- proof
  apply StatMech.FrontierA.triangularPathDisplacement_append l r

/--
[triangularPathVertices_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathVertices_length_eq
  {l : List (Fin 6)} :
-- imply
  (triangularPathVertices l).length = l.length + 1 := by
-- proof
  apply StatMech.FrontierA.triangularPathVertices_length l

/--
[triangularPathVertices_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathVertices_head_eq
  {l : List (Fin 6)} :
-- imply
  (triangularPathVertices l).head? = some 0 := by
-- proof
  apply StatMech.FrontierA.triangularPathVertices_head l

/--
[triangularPathVertices_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathVertices_getLast_eq
  {l : List (Fin 6)} :
-- imply
  (triangularPathVertices l).getLast? = some (triangularPathDisplacement l) := by
-- proof
  apply StatMech.FrontierA.triangularPathVertices_getLast l

/--
[triangularPathVertices_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathVertices_append_eq
  {l r : List (Fin 6)} :
-- imply
  triangularPathVertices (l ++ r) = (triangularPathVertices l).dropLast ++ (triangularPathVertices r).map (triangularPathDisplacement l + ·) := by
-- proof
  apply StatMech.FrontierA.triangularPathVertices_append l r

/--
[triangularPathVertices_append_dropLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathVertices_append_dropLast_eq
  {l r : List (Fin 6)} :
-- imply
  (triangularPathVertices (l ++ r)).dropLast = (triangularPathVertices l).dropLast ++ (triangularPathVertices r).dropLast.map (triangularPathDisplacement l + ·) := by
-- proof
  apply StatMech.FrontierA.triangularPathVertices_append_dropLast l r

/--
[triangularIntStep_axisDirection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularIntStep_axisDirection_eq
  {d : Fin 4} :
-- imply
  triangularIntStep (triangularAxisDirection d) = stepOf d := by
-- proof
  apply StatMech.FrontierA.triangularIntStep_axisDirection d

/--
[triangularPathDisplacement_map_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathDisplacement_map_axis_eq
  {l : List (Fin 4)} :
-- imply
  triangularPathDisplacement (l.map triangularAxisDirection) = ons_pathDisplacement l := by
-- proof
  apply StatMech.FrontierA.triangularPathDisplacement_map_axis l

/--
[triangularPathVertices_map_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathVertices_map_axis_eq
  {l : List (Fin 4)} :
-- imply
  triangularPathVertices (l.map triangularAxisDirection) = ons_pathVertices l := by
-- proof
  apply StatMech.FrontierA.triangularPathVertices_map_axis l

/--
[triangularOutsideConnector_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularOutsideConnector_displacement_eq
  {dx dy top : Int}
-- given
  (hdx : 0 < dx)
  (hdy : dy < top)
  (htop : 0 < top) :
-- imply
  triangularPathDisplacement (triangularOutsideConnector dx dy top) = (-dx, -dy) := by
-- proof
  apply StatMech.FrontierA.triangularOutsideConnector_displacement dx dy top hdx hdy htop

/--
[triangularOutsideConnector_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularOutsideConnector_vertices_dropLast_nodup_eq
  {dx dy top : Int}
-- given
  (hdx : 0 < dx)
  (hdy : dy < top)
  (htop : 0 < top) :
-- imply
  (triangularPathVertices (triangularOutsideConnector dx dy top)).dropLast.Nodup := by
-- proof
  apply StatMech.FrontierA.triangularOutsideConnector_vertices_dropLast_nodup dx dy top hdx hdy htop

/--
[triangularPathDisplacement_not_mem_dropLast_of_vertices_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathDisplacement_not_mem_dropLast_of_vertices_nodup_eq
  {l : List (Fin 6)}
-- given
  (hnodup : (triangularPathVertices l).Nodup) :
-- imply
  triangularPathDisplacement l ∉ (triangularPathVertices l).dropLast := by
-- proof
  apply StatMech.FrontierA.triangularPathDisplacement_not_mem_dropLast_of_vertices_nodup l hnodup

/--
[triangularOutsideConnector_shift_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularOutsideConnector_shift_disjoint_eq
  {l : List (Fin 6)}
  {dx dy top : Int}
-- given
  (hdx : 0 < dx)
  (hdy : dy < top)
  (htop : 0 < top)
  (hdisp : triangularPathDisplacement l = (dx, dy))
  (hnodup : (triangularPathVertices l).Nodup)
  (hxmin : ∀ z ∈ (triangularPathVertices l).dropLast, 0 ≤ z.1)
  (hxmax : ∀ z ∈ (triangularPathVertices l).dropLast, z.1 ≤ dx)
  (hymax : ∀ z ∈ (triangularPathVertices l).dropLast, z.2 < top) :
-- imply
  ∀ z ∈ (triangularPathVertices l).dropLast, ∀ w ∈ (triangularPathVertices (triangularOutsideConnector dx dy top)).dropLast, z ≠ triangularPathDisplacement l + w := by
-- proof
  apply StatMech.FrontierA.triangularOutsideConnector_shift_disjoint l dx dy top hdx hdy htop hdisp hnodup hxmin hxmax hymax

/--
[triangularBoundingClosure_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularBoundingClosure_vertices_dropLast_nodup_eq
  {l : List (Fin 6)}
  {dx dy top : Int}
-- given
  (hdx : 0 < dx)
  (hdy : dy < top)
  (htop : 0 < top)
  (hdisp : triangularPathDisplacement l = (dx, dy))
  (hnodup : (triangularPathVertices l).Nodup)
  (hxmin : ∀ z ∈ (triangularPathVertices l).dropLast, 0 ≤ z.1)
  (hxmax : ∀ z ∈ (triangularPathVertices l).dropLast, z.1 ≤ dx)
  (hymax : ∀ z ∈ (triangularPathVertices l).dropLast, z.2 < top) :
-- imply
  (triangularPathVertices (l ++ triangularOutsideConnector dx dy top)).dropLast.Nodup := by
-- proof
  apply StatMech.FrontierA.triangularBoundingClosure_vertices_dropLast_nodup l dx dy top hdx hdy htop hdisp hnodup hxmin hxmax hymax

/--
[triangularPeriodicIntPos_succ_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicIntPos_succ_cast_eq
  {m : Nat}
  {i : Fin m}
-- given
  (direction : Fin (m + 1) -> Fin 6) :
-- imply
  triangularIntPos direction i.succ = triangularIntPos direction i.castSucc + triangularIntStep (direction i.castSucc) := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicIntPos_succ_cast direction i

/--
[triangularPos_succ_eq_head_add_pos_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPos_succ_eq_head_add_pos_tail_eq
  {n : Nat}
  [NeZero n]
  {i : Fin n}
-- given
  (d : Fin (n + 1) -> Fin 6) :
-- imply
  triangularIntPos d i.succ = triangularIntStep (d 0) + triangularIntPos (fun j : Fin n => d j.succ) i := by
-- proof
  apply StatMech.FrontierA.triangularPos_succ_eq_head_add_pos_tail d i

/--
[triangularPathVertices_dropLast_eq_ofFn_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathVertices_dropLast_eq_ofFn_pos_eq
  {l : List (Fin 6)}
  [NeZero l.length] :
-- imply
  (triangularPathVertices l).dropLast = List.ofFn (triangularIntPos (fun i : Fin l.length => l.get i)) := by
-- proof
  apply StatMech.FrontierA.triangularPathVertices_dropLast_eq_ofFn_pos l

/--
[triangularPos_get_injective_of_vertices_dropLast_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPos_get_injective_of_vertices_dropLast_nodup_eq
  {l : List (Fin 6)}
  [NeZero l.length]
-- given
  (hnodup : (triangularPathVertices l).dropLast.Nodup) :
-- imply
  Function.Injective (triangularIntPos (fun i : Fin l.length => l.get i)) := by
-- proof
  apply StatMech.FrontierA.triangularPos_get_injective_of_vertices_dropLast_nodup l hnodup

/--
[triangularPathDisplacement_eq_sum_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathDisplacement_eq_sum_map_eq
  {l : List (Fin 6)} :
-- imply
  triangularPathDisplacement l = (l.map triangularIntStep).sum := by
-- proof
  apply StatMech.FrontierA.triangularPathDisplacement_eq_sum_map l

/--
[triangularPathDisplacement_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathDisplacement_ofFn_eq
  {n : Nat}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  triangularPathDisplacement (List.ofFn d) = ∑ i, triangularIntStep (d i) := by
-- proof
  apply StatMech.FrontierA.triangularPathDisplacement_ofFn d

/--
[triangularSimpleList_phaseCycle_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularSimpleList_phaseCycle_eq_neg_one_eq
  {l : List (Fin 6)}
  [NeZero l.length]
-- given
  (hclosed : triangularPathDisplacement l = 0)
  (hsimple : (triangularPathVertices l).dropLast.Nodup)
  (hlen : 3 ≤ l.length) :
-- imply
  kwVectorPhaseCycle (l.map triangularIntVector) = -1 := by
-- proof
  apply StatMech.FrontierA.triangularSimpleList_phaseCycle_eq_neg_one l hclosed hsimple hlen

/--
[triangularPeriodStateList_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodStateList_isChain_eq
  {n : Nat}
  [NeZero n]
  {r : Nat}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  List.IsChain (fun a b => triangularPeriodStateCoord d b = triangularPeriodStateCoord d a + triangularIntStep (d a.2)) (ons_periodStateList n r) := by
-- proof
  apply StatMech.FrontierA.triangularPeriodStateList_isChain d r

/--
[triangularPeriodState_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodState_boundary_eq
  {m : Nat}
  {r : Nat}
-- given
  (d : Fin (m + 1) -> Fin 6) :
-- imply
  triangularPeriodStateCoord d (r + 1, 0) = triangularPeriodStateCoord d (r, Fin.last m) + triangularIntStep (d (Fin.last m)) := by
-- proof
  apply StatMech.FrontierA.triangularPeriodState_boundary d r

/--
[triangularAllPeriodStates_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularAllPeriodStates_isChain_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  List.IsChain (fun a b => triangularPeriodStateCoord d b = triangularPeriodStateCoord d a + triangularIntStep (d a.2)) (ons_allPeriodStates n N) := by
-- proof
  apply StatMech.FrontierA.triangularAllPeriodStates_isChain d N

/--
[triangularPeriodicArcStates_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicArcStates_isChain_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
  {imin imax : Fin n}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  List.IsChain (fun a b => triangularPeriodStateCoord d b = triangularPeriodStateCoord d a + triangularIntStep (d a.2)) (ons_periodicArcStates N imin imax) := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicArcStates_isChain d N imin imax

/--
[triangularPathVertices_map_dropLast_of_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathVertices_map_dropLast_of_chain_eq
  [Inhabited X]
  {s : List X}
-- given
  (coord : X -> Int × Int)
  (dir : X -> Fin 6)
  (hs : s ≠ [])
  (hchain : List.IsChain (fun a b => coord b = coord a + triangularIntStep (dir a)) s) :
-- imply
  triangularPathVertices (s.dropLast.map dir) = s.map (fun x => coord x - coord s.head!) := by
-- proof
  apply StatMech.FrontierA.triangularPathVertices_map_dropLast_of_chain coord dir s hs hchain

/--
[triangularPeriodicArc_pathVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicArc_pathVertices_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
  {imin imax : Fin n}
-- given
  (d : Fin n -> Fin 6)
  (hN : 1 ≤ N) :
-- imply
  triangularPathVertices (triangularPeriodicArcDirections d N imin imax) = (ons_periodicArcStates N imin imax).map (fun z => triangularPeriodStateCoord d z - triangularPeriodStateCoord d (0, imin)) := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicArc_pathVertices d N hN imin imax

/--
[triangularPeriodicArc_pathVertices_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicArc_pathVertices_nodup_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
  {imin imax : Fin n}
-- given
  (d : Fin n -> Fin 6)
  (hN : 1 ≤ N)
  (hinj : Function.Injective (triangularPeriodStateCoord d)) :
-- imply
  (triangularPathVertices (triangularPeriodicArcDirections d N imin imax)).Nodup := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicArc_pathVertices_nodup d N hN imin imax hinj

/--
[triangularPeriodicArc_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicArc_displacement_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
  {imin imax : Fin n}
-- given
  (d : Fin n -> Fin 6)
  (hN : 1 ≤ N) :
-- imply
  triangularPathDisplacement (triangularPeriodicArcDirections d N imin imax) = triangularPeriodStateCoord d (N, imax) - triangularPeriodStateCoord d (0, imin) := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicArc_displacement d N hN imin imax

/--
[triangularPeriodicArc_xmin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicArc_xmin_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
  {imin imax : Fin n}
-- given
  (d : Fin n -> Fin 6)
  (hN : 1 ≤ N)
  (hmin : ∀ i, (triangularIntPos d imin).1 ≤ (triangularIntPos d i).1)
  (hD : 0 < (triangularPathDisplacement (List.ofFn d)).1) :
-- imply
  ∀ z ∈ (triangularPathVertices (triangularPeriodicArcDirections d N imin imax)).dropLast, 0 ≤ z.1 := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicArc_xmin d N hN imin imax hmin hD

/--
[triangularPeriodicArc_xmax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicArc_xmax_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
  {imin imax : Fin n}
-- given
  (d : Fin n -> Fin 6)
  (hN : 1 ≤ N)
  (hmax : ∀ i, (triangularIntPos d i).1 ≤ (triangularIntPos d imax).1)
  (hD : 0 < (triangularPathDisplacement (List.ofFn d)).1) :
-- imply
  ∀ z ∈ (triangularPathVertices (triangularPeriodicArcDirections d N imin imax)).dropLast, z.1 ≤ (triangularPeriodStateCoord d (N, imax) - triangularPeriodStateCoord d (0, imin)).1 := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicArc_xmax d N hN imin imax hmax hD

/--
[triangularExists_path_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularExists_path_top_eq
  {l : List (Fin 6)}
  {dy : Int} :
-- imply
  ∃ top : Int, 0 < top ∧ dy < top ∧ ∀ z ∈ (triangularPathVertices l).dropLast, z.2 < top := by
-- proof
  apply StatMech.FrontierA.triangularExists_path_top l dy

/--
[triangularPeriodicArc_closure_phase_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicArc_closure_phase_eq_neg_one_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
  {imin imax : Fin n}
-- given
  (d : Fin n -> Fin 6)
  (hN : 1 ≤ N)
  (hinj : Function.Injective (triangularPeriodStateCoord d))
  (hmin : ∀ i, (triangularIntPos d imin).1 ≤ (triangularIntPos d i).1)
  (hmax : ∀ i, (triangularIntPos d i).1 ≤ (triangularIntPos d imax).1)
  (hD : 0 < (triangularPathDisplacement (List.ofFn d)).1) :
-- imply
  let l := triangularPeriodicArcDirections d N imin imax let delta := triangularPeriodStateCoord d (N, imax) - triangularPeriodStateCoord d (0, imin) let top := Classical.choose (triangularExists_path_top l delta.2) kwVectorPhaseCycle ((l ++ triangularOutsideConnector delta.1 delta.2 top).map triangularIntVector) = -1 := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicArc_closure_phase_eq_neg_one d N hN imin imax hinj hmin hmax hD

/--
[kwVectorPhasePath_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma kwVectorPhasePath_append_eq
  {l r : List Complex}
-- given
  (hl : l ≠ [])
  (hr : r ≠ []) :
-- imply
  kwVectorPhasePath (l ++ r) = kwVectorPhasePath l * kwVectorTurnPhase l.getLast! r.head! * kwVectorPhasePath r := by
-- proof
  apply StatMech.FrontierA.kwVectorPhasePath_append l r hl hr

/--
[kwVectorPhaseCycle_eq_path_mul_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_eq_path_mul_turn_eq
  {l : List Complex}
-- given
  (hl : l ≠ []) :
-- imply
  kwVectorPhaseCycle l = kwVectorPhasePath l * kwVectorTurnPhase l.getLast! l.head! := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_eq_path_mul_turn l hl

/--
[kwVectorPhaseCycle_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_append_eq
  {l r : List Complex}
-- given
  (hl : l ≠ [])
  (hr : r ≠ []) :
-- imply
  kwVectorPhaseCycle (l ++ r) = kwVectorPhasePath l * kwVectorTurnPhase l.getLast! r.head! * kwVectorPhasePath r * kwVectorTurnPhase r.getLast! l.head! := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_append l r hl hr

/--
[map_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma map_head_eq
  [Inhabited X]
  [Inhabited Y]
  {l : List X}
-- given
  (f : X -> Y)
  (hl : l ≠ []) :
-- imply
  (l.map f).head! = f l.head! := by
-- proof
  apply StatMech.FrontierA.map_head f l hl

/--
[map_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma map_getLast_eq
  [Inhabited X]
  [Inhabited Y]
  {l : List X}
-- given
  (f : X -> Y)
  (hl : l ≠ []) :
-- imply
  (l.map f).getLast! = f l.getLast! := by
-- proof
  apply StatMech.FrontierA.map_getLast f l hl

/--
[kwVectorPhasePath_replicate_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma kwVectorPhasePath_replicate_succ_eq
  {n : Nat}
  {x : Complex} :
-- imply
  kwVectorPhasePath (List.replicate (n + 1) x) = 1 := by
-- proof
  apply StatMech.FrontierA.kwVectorPhasePath_replicate_succ n x

/--
[getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma getLast_eq
  [Inhabited X]
  {n : Nat}
  {x : X} :
-- imply
  (List.replicate (n + 1) x).getLast! = x := by
-- proof
  apply StatMech.FrontierA.getLast n x

/--
[kwVectorPhasePath_five_blocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma kwVectorPhasePath_five_blocks_eq
  {a b c d e : Complex}
  {na nb nc nd ne : Nat} :
-- imply
  kwVectorPhasePath (List.replicate (na + 1) a ++ List.replicate (nb + 1) b ++ List.replicate (nc + 1) c ++ List.replicate (nd + 1) d ++ List.replicate (ne + 1) e) = kwVectorTurnPhase a b * kwVectorTurnPhase b c * kwVectorTurnPhase c d * kwVectorTurnPhase d e := by
-- proof
  apply StatMech.FrontierA.kwVectorPhasePath_five_blocks a b c d e na nb nc nd ne

/--
[triangularOutsideConnector_phasePath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularOutsideConnector_phasePath_eq
  {dx dy top : Int}
-- given
  (hdx : 0 < dx)
  (hdy : dy < top)
  (htop : 0 < top) :
-- imply
  kwVectorPhasePath ((triangularOutsideConnector dx dy top).map triangularIntVector) = kwVectorTurnPhase (triangularIntVector 1) (triangularIntVector 3) * kwVectorTurnPhase (triangularIntVector 3) (triangularIntVector 0) * kwVectorTurnPhase (triangularIntVector 0) (triangularIntVector 2) * kwVectorTurnPhase (triangularIntVector 2) (triangularIntVector 1) := by
-- proof
  apply StatMech.FrontierA.triangularOutsideConnector_phasePath dx dy top hdx hdy htop

/--
[triangularOutsideConnector_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularOutsideConnector_head_eq
  {dx dy top : Int} :
-- imply
  (triangularOutsideConnector dx dy top).head! = 1 := by
-- proof
  apply StatMech.FrontierA.triangularOutsideConnector_head dx dy top

/--
[triangularOutsideConnector_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularOutsideConnector_getLast_eq
  {dx dy top : Int} :
-- imply
  (triangularOutsideConnector dx dy top).getLast! = 1 := by
-- proof
  apply StatMech.FrontierA.triangularOutsideConnector_getLast dx dy top

/--
[triangularOfFn_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularOfFn_ne_nil_eq
  {n : Nat}
  [NeZero n]
-- given
  (d : Fin n -> Fin 6) :
-- imply
  List.ofFn d ≠ [] := by
-- proof
  apply StatMech.FrontierA.triangularOfFn_ne_nil d

/--
[triangularDrop_ofFn_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularDrop_ofFn_ne_nil_eq
  {n : Nat}
  [NeZero n]
  {i : Fin n}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  (List.ofFn d).drop i.val ≠ [] := by
-- proof
  apply StatMech.FrontierA.triangularDrop_ofFn_ne_nil d i

/--
[triangularDirectionPeriods_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularDirectionPeriods_length_eq
  {n : Nat}
  {N : Nat}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  (triangularDirectionPeriods d N).length = N * n := by
-- proof
  apply StatMech.FrontierA.triangularDirectionPeriods_length d N

/--
[triangularAllPeriodStates_map_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularAllPeriodStates_map_direction_eq
  {n : Nat}
  {N : Nat}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  (ons_allPeriodStates n N).map (fun z => d z.2) = triangularDirectionPeriods d (N + 1) := by
-- proof
  apply StatMech.FrontierA.triangularAllPeriodStates_map_direction d N

/--
[triangularPeriodicArcDirections_eq_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicArcDirections_eq_slice_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
  {imin imax : Fin n}
-- given
  (d : Fin n -> Fin 6)
  (hN : 1 ≤ N) :
-- imply
  triangularPeriodicArcDirections d N imin imax = ((triangularDirectionPeriods d (N + 1)).drop imin.val).take (N * n + imax.val - imin.val) := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicArcDirections_eq_slice d N hN imin imax

/--
[triangularDirectionPeriods_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularDirectionPeriods_succ_eq
  {n : Nat}
  {N : Nat}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  triangularDirectionPeriods d (N + 1) = triangularDirectionPeriods d N ++ List.ofFn d := by
-- proof
  apply StatMech.FrontierA.triangularDirectionPeriods_succ d N

/--
[triangularDirectionPeriods_append_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularDirectionPeriods_append_comm_eq
  {n : Nat}
  {N : Nat}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  triangularDirectionPeriods d N ++ List.ofFn d = List.ofFn d ++ triangularDirectionPeriods d N := by
-- proof
  apply StatMech.FrontierA.triangularDirectionPeriods_append_comm d N

/--
[triangularDirectionPeriods_succ_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularDirectionPeriods_succ_left_eq
  {n : Nat}
  {N : Nat}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  triangularDirectionPeriods d (N + 1) = List.ofFn d ++ triangularDirectionPeriods d N := by
-- proof
  apply StatMech.FrontierA.triangularDirectionPeriods_succ_left d N

/--
[triangularPeriodicArcDirections_eq_blocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicArcDirections_eq_blocks_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
  {imin imax : Fin n}
-- given
  (d : Fin n -> Fin 6)
  (hN : 1 ≤ N) :
-- imply
  triangularPeriodicArcDirections d N imin imax = (List.ofFn d).drop imin.val ++ triangularDirectionPeriods d (N - 1) ++ (List.ofFn d).take imax.val := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicArcDirections_eq_blocks d N hN imin imax

/--
[triangularDrop_ofFn_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularDrop_ofFn_getLast_eq
  {n : Nat}
  [NeZero n]
  {i : Fin n}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  ((List.ofFn d).drop i.val).getLast! = (List.ofFn d).getLast! := by
-- proof
  apply StatMech.FrontierA.triangularDrop_ofFn_getLast d i

/--
[triangularDirectionPeriods_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularDirectionPeriods_getLast_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
-- given
  (d : Fin n -> Fin 6)
  (hN : 1 ≤ N) :
-- imply
  (triangularDirectionPeriods d N).getLast! = (List.ofFn d).getLast! := by
-- proof
  apply StatMech.FrontierA.triangularDirectionPeriods_getLast d N hN

/--
[triangularArcInitialBlock_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularArcInitialBlock_getLast_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
  {imin : Fin n}
-- given
  (d : Fin n -> Fin 6)
  (hN : 1 ≤ N) :
-- imply
  ((List.ofFn d).drop imin.val ++ triangularDirectionPeriods d (N - 1)).getLast! = (List.ofFn d).getLast! := by
-- proof
  apply StatMech.FrontierA.triangularArcInitialBlock_getLast d N hN imin

/--
[triangularTake_ofFn_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularTake_ofFn_head_eq
  {n : Nat}
  [NeZero n]
  {i : Fin n}
-- given
  (d : Fin n -> Fin 6)
  (h : (List.ofFn d).take i.val ≠ []) :
-- imply
  ((List.ofFn d).take i.val).head! = (List.ofFn d).head! := by
-- proof
  apply StatMech.FrontierA.triangularTake_ofFn_head d i h

/--
[kwVectorPhasePath_insert_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma kwVectorPhasePath_insert_cycle_eq
  {A D P : List Complex}
-- given
  (hA : A ≠ [])
  (hD : D ≠ [])
  (hlast : A.getLast! = D.getLast!)
  (hhead : P ≠ [] -> P.head! = D.head!) :
-- imply
  kwVectorPhasePath (A ++ D ++ P) = kwVectorPhasePath (A ++ P) * kwVectorPhaseCycle D := by
-- proof
  apply StatMech.FrontierA.kwVectorPhasePath_insert_cycle A D P hA hD hlast hhead

/--
[triangularPeriodicArc_phasePath_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicArc_phasePath_succ_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
  {imin imax : Fin n}
-- given
  (d : Fin n -> Fin 6)
  (hN : 1 ≤ N) :
-- imply
  let old := triangularPeriodicArcDirections d N imin imax let new := triangularPeriodicArcDirections d (N + 1) imin imax kwVectorPhasePath (new.map triangularIntVector) = kwVectorPhasePath (old.map triangularIntVector) * kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector) := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicArc_phasePath_succ d N hN imin imax

/--
[triangularPeriodicArc_head_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicArc_head_succ_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
  {imin imax : Fin n}
-- given
  (d : Fin n -> Fin 6)
  (hN : 1 ≤ N) :
-- imply
  (triangularPeriodicArcDirections d (N + 1) imin imax).head! = (triangularPeriodicArcDirections d N imin imax).head! := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicArc_head_succ d N hN imin imax

/--
[triangularPeriodicArc_getLast_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicArc_getLast_succ_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
  {imin imax : Fin n}
-- given
  (d : Fin n -> Fin 6)
  (hN : 1 ≤ N) :
-- imply
  (triangularPeriodicArcDirections d (N + 1) imin imax).getLast! = (triangularPeriodicArcDirections d N imin imax).getLast! := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicArc_getLast_succ d N hN imin imax

/--
[triangularPeriodicArc_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicArc_ne_nil_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
  {imin imax : Fin n}
-- given
  (d : Fin n -> Fin 6)
  (hN : 1 ≤ N) :
-- imply
  triangularPeriodicArcDirections d N imin imax ≠ [] := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicArc_ne_nil d N hN imin imax

/--
[triangularPeriodicClosure_phase_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicClosure_phase_succ_eq
  {n : Nat}
  [NeZero n]
  {N : Nat}
  {imin imax : Fin n}
  {dx dy top dx' dy' top' : Int}
-- given
  (d : Fin n -> Fin 6)
  (hN : 1 ≤ N)
  (hdx : 0 < dx)
  (hdy : dy < top)
  (htop : 0 < top)
  (hdx' : 0 < dx')
  (hdy' : dy' < top')
  (htop' : 0 < top') :
-- imply
  let old := triangularPeriodicArcDirections d N imin imax let new := triangularPeriodicArcDirections d (N + 1) imin imax kwVectorPhaseCycle ((new ++ triangularOutsideConnector dx' dy' top').map triangularIntVector) = kwVectorPhaseCycle ((old ++ triangularOutsideConnector dx dy top).map triangularIntVector) * kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector) := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicClosure_phase_succ d N hN imin imax dx dy top dx' dy' top' hdx hdy htop hdx' hdy' htop'

/--
[triangularPeriodicSimple_phaseCycle_eq_one_of_pos_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicSimple_phaseCycle_eq_one_of_pos_x_eq
  {n : Nat}
  [NeZero n]
-- given
  (d : Fin n -> Fin 6)
  (hinj : Function.Injective (triangularPeriodStateCoord d))
  (hD : 0 < (triangularPathDisplacement (List.ofFn d)).1) :
-- imply
  kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector) = 1 := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicSimple_phaseCycle_eq_one_of_pos_x d hinj hD

/--
[triangularIntStep_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularIntStep_opposite_eq
  {a : Fin 6} :
-- imply
  triangularIntStep (triangularTorusDirectionReverse a) = -triangularIntStep a := by
-- proof
  apply StatMech.FrontierA.triangularIntStep_opposite a

/--
[triangularIntStep_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularIntStep_swap_eq
  {a : Fin 6} :
-- imply
  triangularIntStep (triangularSwapDirection a) = triangularSwapPoint (triangularIntStep a) := by
-- proof
  apply StatMech.FrontierA.triangularIntStep_swap a

/--
[triangularIntPos_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularIntPos_opposite_eq
  {n : Nat}
  [NeZero n]
  {i : Fin n}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  triangularIntPos (fun k => triangularTorusDirectionReverse (d k)) i = -triangularIntPos d i := by
-- proof
  apply StatMech.FrontierA.triangularIntPos_opposite d i

/--
[triangularIntPos_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularIntPos_swap_eq
  {n : Nat}
  [NeZero n]
  {i : Fin n}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  triangularIntPos (fun k => triangularSwapDirection (d k)) i = triangularSwapPoint (triangularIntPos d i) := by
-- proof
  apply StatMech.FrontierA.triangularIntPos_swap d i

/--
[triangularPathDisplacement_ofFn_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathDisplacement_ofFn_opposite_eq
  {n : Nat}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  triangularPathDisplacement (List.ofFn (fun k => triangularTorusDirectionReverse (d k))) = -triangularPathDisplacement (List.ofFn d) := by
-- proof
  apply StatMech.FrontierA.triangularPathDisplacement_ofFn_opposite d

/--
[triangularPathDisplacement_ofFn_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPathDisplacement_ofFn_swap_eq
  {n : Nat}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  triangularPathDisplacement (List.ofFn (fun k => triangularSwapDirection (d k))) = triangularSwapPoint (triangularPathDisplacement (List.ofFn d)) := by
-- proof
  apply StatMech.FrontierA.triangularPathDisplacement_ofFn_swap d

/--
[triangularPeriodStateCoord_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodStateCoord_opposite_eq
  {n : Nat}
  [NeZero n]
  {z : Nat × Fin n}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  triangularPeriodStateCoord (fun k => triangularTorusDirectionReverse (d k)) z = -triangularPeriodStateCoord d z := by
-- proof
  apply StatMech.FrontierA.triangularPeriodStateCoord_opposite d z

/--
[triangularPeriodStateCoord_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodStateCoord_swap_eq
  {n : Nat}
  [NeZero n]
  {z : Nat × Fin n}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  triangularPeriodStateCoord (fun k => triangularSwapDirection (d k)) z = triangularSwapPoint (triangularPeriodStateCoord d z) := by
-- proof
  apply StatMech.FrontierA.triangularPeriodStateCoord_swap d z

/--
[triangularPeriodStateCoord_opposite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodStateCoord_opposite_injective_eq
  {n : Nat}
  [NeZero n]
-- given
  (d : Fin n -> Fin 6)
  (hinj : Function.Injective (triangularPeriodStateCoord d)) :
-- imply
  Function.Injective (triangularPeriodStateCoord (fun k => triangularTorusDirectionReverse (d k))) := by
-- proof
  apply StatMech.FrontierA.triangularPeriodStateCoord_opposite_injective d hinj

/--
[triangularPeriodStateCoord_swap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodStateCoord_swap_injective_eq
  {n : Nat}
  [NeZero n]
-- given
  (d : Fin n -> Fin 6)
  (hinj : Function.Injective (triangularPeriodStateCoord d)) :
-- imply
  Function.Injective (triangularPeriodStateCoord (fun k => triangularSwapDirection (d k))) := by
-- proof
  apply StatMech.FrontierA.triangularPeriodStateCoord_swap_injective d hinj

/--
[kwVectorTurnPhase_triangular_eq_exp_turnExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma kwVectorTurnPhase_triangular_eq_exp_turnExponent_eq
  {a b : Fin 6}
-- given
  (hne : b ≠ triangularTorusDirectionReverse a) :
-- imply
  kwVectorTurnPhase (triangularIntVector a) (triangularIntVector b) = Complex.exp ((((triangularTorusTurnExponent a b : Int) : Real) * (Real.pi / 4) : Complex) * Complex.I / 2) := by
-- proof
  apply StatMech.FrontierA.kwVectorTurnPhase_triangular_eq_exp_turnExponent a b hne

/--
[triangularTurnExponent_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularTurnExponent_opposite_eq
  {a b : Fin 6}
-- given
  (hne : b ≠ triangularTorusDirectionReverse a) :
-- imply
  triangularTorusTurnExponent (triangularTorusDirectionReverse a) (triangularTorusDirectionReverse b) = triangularTorusTurnExponent a b := by
-- proof
  apply StatMech.FrontierA.triangularTurnExponent_opposite a b hne

/--
[triangularTurnExponent_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularTurnExponent_swap_eq
  {a b : Fin 6}
-- given
  (hne : b ≠ triangularTorusDirectionReverse a) :
-- imply
  triangularTorusTurnExponent (triangularSwapDirection a) (triangularSwapDirection b) = -triangularTorusTurnExponent a b := by
-- proof
  apply StatMech.FrontierA.triangularTurnExponent_swap a b hne

/--
[triangularSwapDirection_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularSwapDirection_reverse_eq
  {a : Fin 6} :
-- imply
  triangularSwapDirection (triangularTorusDirectionReverse a) = triangularTorusDirectionReverse (triangularSwapDirection a) := by
-- proof
  apply StatMech.FrontierA.triangularSwapDirection_reverse a

/--
[triangularSwapDirection_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularSwapDirection_injective_eq :
-- imply
  Function.Injective triangularSwapDirection := by
-- proof
  apply StatMech.FrontierA.triangularSwapDirection_injective

/--
[triangularOppositeDirection_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularOppositeDirection_reverse_eq
  {a : Fin 6} :
-- imply
  triangularTorusDirectionReverse (triangularTorusDirectionReverse a) = a := by
-- proof
  apply StatMech.FrontierA.triangularOppositeDirection_reverse a

/--
[triangularDirection_nonbacktracking_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularDirection_nonbacktracking_opposite_eq
  {n : Nat}
  [NeZero n]
-- given
  (d : Fin n -> Fin 6)
  (hnb : ∀ k, d (k + 1) ≠ triangularTorusDirectionReverse (d k)) :
-- imply
  ∀ k, triangularTorusDirectionReverse (d (k + 1)) ≠ triangularTorusDirectionReverse (triangularTorusDirectionReverse (d k)) := by
-- proof
  apply StatMech.FrontierA.triangularDirection_nonbacktracking_opposite d hnb

/--
[triangularDirection_nonbacktracking_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularDirection_nonbacktracking_swap_eq
  {n : Nat}
  [NeZero n]
-- given
  (d : Fin n -> Fin 6)
  (hnb : ∀ k, d (k + 1) ≠ triangularTorusDirectionReverse (d k)) :
-- imply
  ∀ k, triangularSwapDirection (d (k + 1)) ≠ triangularTorusDirectionReverse (triangularSwapDirection (d k)) := by
-- proof
  apply StatMech.FrontierA.triangularDirection_nonbacktracking_swap d hnb

/--
[triangularPhaseCycle_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPhaseCycle_opposite_eq
  {n : Nat}
  [NeZero n]
-- given
  (d : Fin n -> Fin 6)
  (hnb : ∀ k, d (k + 1) ≠ triangularTorusDirectionReverse (d k)) :
-- imply
  kwVectorPhaseCycle ((List.ofFn (fun k => triangularTorusDirectionReverse (d k))).map triangularIntVector) = kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector) := by
-- proof
  apply StatMech.FrontierA.triangularPhaseCycle_opposite d hnb

/--
[triangularPhaseCycle_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPhaseCycle_swap_eq
  {n : Nat}
  [NeZero n]
-- given
  (d : Fin n -> Fin 6)
  (hnb : ∀ k, d (k + 1) ≠ triangularTorusDirectionReverse (d k)) :
-- imply
  kwVectorPhaseCycle ((List.ofFn (fun k => triangularSwapDirection (d k))).map triangularIntVector) = (kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector))⁻¹ := by
-- proof
  apply StatMech.FrontierA.triangularPhaseCycle_swap d hnb

/--
[triangularPeriodicSimple_phaseCycle_eq_one_of_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodicSimple_phaseCycle_eq_one_of_nonzero_eq
  {n : Nat}
  [NeZero n]
-- given
  (d : Fin n -> Fin 6)
  (hinj : Function.Injective (triangularPeriodStateCoord d))
  (hnb : ∀ k, d (k + 1) ≠ triangularTorusDirectionReverse (d k))
  (hne : (triangularPathDisplacement (List.ofFn d)).1 ≠ 0 ∨ (triangularPathDisplacement (List.ofFn d)).2 ≠ 0) :
-- imply
  kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector) = 1 := by
-- proof
  apply StatMech.FrontierA.triangularPeriodicSimple_phaseCycle_eq_one_of_nonzero d hinj hnb hne

/--
[exists_triangularTurnExponent_sum_eq_eight_mul_even_of_phase_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma exists_triangularTurnExponent_sum_eq_eight_mul_even_of_phase_one_eq
  {n : Nat}
  [NeZero n]
-- given
  (direction : Fin n -> Fin 6)
  (hnonbacktracking : ∀ k, direction (k + 1) ≠ triangularTorusDirectionReverse (direction k))
  (hphase : kwVectorPhaseCycle ((List.ofFn direction).map triangularIntVector) = 1) :
-- imply
  ∃ m : Int, (∑ k, triangularTorusTurnExponent (direction k) (direction (k + 1))) = 8 * (2 * m) := by
-- proof
  apply StatMech.FrontierA.exists_triangularTurnExponent_sum_eq_eight_mul_even_of_phase_one direction hnonbacktracking hphase

/--
[triangularPeriodStateCoord_eq_intPeriodicPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodStateCoord_eq_intPeriodicPos_eq
  {n : Nat}
  [NeZero n]
  {z : Nat × Fin n}
-- given
  (d : Fin n -> Fin 6) :
-- imply
  triangularPeriodStateCoord d z = triangularIntPeriodicPos d ((z.1 : Int), z.2) := by
-- proof
  apply StatMech.FrontierA.triangularPeriodStateCoord_eq_intPeriodicPos d z

/--
[triangularPeriodStateCoord_injective_of_intPeriodicPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularPeriodStateCoord_injective_of_intPeriodicPos_eq
  {n : Nat}
  [NeZero n]
-- given
  (d : Fin n -> Fin 6)
  (hinj : Function.Injective (triangularIntPeriodicPos d)) :
-- imply
  Function.Injective (triangularPeriodStateCoord d) := by
-- proof
  apply StatMech.FrontierA.triangularPeriodStateCoord_injective_of_intPeriodicPos d hinj

/--
[triangularTorus_cyclePhaseProduct_eq_one_of_nonzeroHomology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularTorus_cyclePhaseProduct_eq_one_of_nonzeroHomology_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hp : p.IsCycle)
  (hhom : surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L) p.edges.toFinset ≠ 0) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1) (kwGraphCycleDartLoop p) = 1 := by
-- proof
  apply StatMech.FrontierA.triangularTorus_cyclePhaseProduct_eq_one_of_nonzeroHomology L rho hrho p hp hhom

/--
[triangularTorus_baseSpinSign_eq_if_homology_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean)
-/
@[path]
private lemma triangularTorus_baseSpinSign_eq_if_homology_zero_eq
-- given
  (h : SurfaceHomology 1) :
-- imply
  (surfaceParitySign (surfaceQuadraticParity (triangularTorusSurfaceSpin 0 0) h) : Complex) = if h = 0 then 1 else -1 := by
-- proof
  apply StatMech.FrontierA.triangularTorus_baseSpinSign_eq_if_homology_zero h


-- created on 2026-10-23
