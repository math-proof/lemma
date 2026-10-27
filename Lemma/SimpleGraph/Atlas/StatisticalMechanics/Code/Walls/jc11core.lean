import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc11core
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[jc11_dartFace_extremeBase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_dartFace_extremeBase_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  dartFace (extremeBase K c hc).1 = ![c 0 - 1, c 1 - 1] := by
-- proof
  apply StatMech.Walls.jc11_dartFace_extremeBase K c hc

/--
[jc11_dartNext_extremeBase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_dartNext_extremeBase_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  dartNext K (leftDart c) = mkDart c ![0, 1] (by simp [unitWt, Fin.sum_univ_two]) := by
-- proof
  apply StatMech.Walls.jc11_dartNext_extremeBase K c hc

/--
[jc11_dartNext_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_dartNext_dir_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  (dartNext K (leftDart c)).dir = ![0, 1] := by
-- proof
  apply StatMech.Walls.jc11_dartNext_dir K c hc

/--
[jc11_dartNext_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_dartNext_tail_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  (dartNext K (leftDart c)).tail = c := by
-- proof
  apply StatMech.Walls.jc11_dartNext_tail K c hc

/--
[jc11_dartFace_dartNext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_dartFace_dartNext_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  dartFace (dartNext K (leftDart c)) = ![c 0 - 1, c 1] := by
-- proof
  apply StatMech.Walls.jc11_dartFace_dartNext K c hc

/--
[jc11_dartNext_travel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_dartNext_travel_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  -rot90Fun (dartNext K (leftDart c)).dir = (![1, 0] : Site 2) := by
-- proof
  apply StatMech.Walls.jc11_dartNext_travel K c hc

/--
[jc11_dartNext_front_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_dartNext_front_nmem_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  (dartNext K (leftDart c)).head + (-rot90Fun (dartNext K (leftDart c)).dir) ∉ K := by
-- proof
  apply StatMech.Walls.jc11_dartNext_front_nmem K c hc

/--
[jc11_dartFace_dartNext2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_dartFace_dartNext2_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  dartFace (dartNext K (dartNext K (leftDart c))) = ![c 0, c 1] := by
-- proof
  apply StatMech.Walls.jc11_dartFace_dartNext2 K c hc

/--
[jc11_dartFace_eq_aboveLeft_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_dartFace_eq_aboveLeft_unique_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {e : Dart}
-- given
  (hc : IsExtremeCell K c)
  (he : IsBoundaryDart K e)
  (hf : dartFace e = ![c 0 - 1, c 1]) :
-- imply
  e = mkDart c ![0, 1] (by simp [unitWt, Fin.sum_univ_two]) := by
-- proof
  apply StatMech.Walls.jc11_dartFace_eq_aboveLeft_unique K c hc e he hf

/--
[jc11_orbit_face_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_orbit_face_one_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c) :
-- imply
  dartFace ((dartNext K)^[1] (extremeBase K c hc).1) = ![c 0 - 1, c 1] := by
-- proof
  apply StatMech.Walls.jc11_orbit_face_one K c hc

/--
[jc11_face_aboveLeft_index_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_face_aboveLeft_index_eq_one_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {m : ℕ}
-- given
  (hK : K.Finite)
  (hc : IsExtremeCell K c)
  (hm1 : 1 ≤ m)
  (hmp : m ≤ dartOrbitPeriod K (extremeBase K c hc))
  (hf : dartFace ((dartNext K)^[m] (extremeBase K c hc).1) = ![c 0 - 1, c 1]) :
-- imply
  m = 1 := by
-- proof
  apply StatMech.Walls.jc11_face_aboveLeft_index_eq_one K hK c hc m hm1 hmp hf

/--
[jc11_orbitLoop_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_orbitLoop_edges_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (mpl_orbitLoop K a).edges = (List.range (dartOrbitPeriod K a)).map (fun k => s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1))) := by
-- proof
  apply StatMech.Walls.jc11_orbitLoop_edges K a

/--
[jc11_face_eq_aboveLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_face_eq_aboveLeft_eq
  {f : Site 2}
  {c : Site 2}
-- given
  (h0 : f 0 = c 0 - 1)
  (h1 : f 1 = c 1) :
-- imply
  f = (![c 0 - 1, c 1] : Site 2) := by
-- proof
  apply StatMech.Walls.jc11_face_eq_aboveLeft f c h0 h1

/--
[jc11_topWall_iff_index_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_topWall_iff_index_one_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {k : ℕ}
-- given
  (hK : K.Finite)
  (hc : IsExtremeCell K c)
  (hk : k < dartOrbitPeriod K (extremeBase K c hc)) :
-- imply
  jc10core_topWallEdge c s(dartFace ((dartNext K)^[k] (extremeBase K c hc).1), dartFace ((dartNext K)^[k + 1] (extremeBase K c hc).1)) ↔ k = 1 := by
-- proof
  apply StatMech.Walls.jc11_topWall_iff_index_one K hK c hc k hk

/--
[jc11_two_le_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_two_le_period_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite) :
-- imply
  2 ≤ dartOrbitPeriod K a := by
-- proof
  apply StatMech.Walls.jc11_two_le_period K hK a

/--
[jc11_range_countP_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_range_countP_eq_one_eq
  {p : ℕ}
-- given
  (hp : 1 < p) :
-- imply
  (List.range p).countP (fun k => decide (k = 1)) = 1 := by
-- proof
  apply StatMech.Walls.jc11_range_countP_eq_one p hp

/--
[jc11_topWallCount_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_topWallCount_eq_one_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hc : IsExtremeCell K c) :
-- imply
  jc10core_topWallCount c (mpl_orbitLoop K (extremeBase K c hc)) = 1 := by
-- proof
  apply StatMech.Walls.jc11_topWallCount_eq_one K hK c hc

/--
[jc11_TopWallOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_TopWallOdd_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hc : IsExtremeCell K c) :
-- imply
  jc10core_TopWallOdd K (extremeBase K c hc) c := by
-- proof
  apply StatMech.Walls.jc11_TopWallOdd K hK c hc

/--
[jc11_cornerCellOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_cornerCellOdd_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hc : IsExtremeCell K c) :
-- imply
  ¬ Even (jec_rayCount c (mpl_orbitLoop K (extremeBase K c hc))) := by
-- proof
  apply StatMech.Walls.jc11_cornerCellOdd K hK c hc

/--
[jc11_exists_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc11core.lean)
-/
@[path]
private lemma jc11_exists_windingWitness_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ c : Site 2, ∃ hc : IsExtremeCell K c, c ∈ K ∧ ¬ Even (jec_rayCount c (mpl_orbitLoop K (extremeBase K c hc))) := by
-- proof
  apply StatMech.Walls.jc11_exists_windingWitness K hK hne


-- created on 2026-10-23
