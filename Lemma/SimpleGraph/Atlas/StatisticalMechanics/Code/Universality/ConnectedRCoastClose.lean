import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
open Set SimpleGraph MeasureTheory ProbabilityTheory StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[crr_rightComplement_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_rightComplement_closed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c c' : Site 2}
-- given
  (hc : c ∈ bac_rightComplement ω n)
  (hadj : (hypercubicLattice 2).Adj c c')
  (hc'box : c' ∈ rect 0 n 0 n)
  (hc'L : c' ∉ bcd_leftReach ω n) :
-- imply
  c' ∈ bac_rightComplement ω n := by
-- proof
  apply StatMech.Universality.crr_rightComplement_closed ω n hc hadj hc'box hc'L

/--
[crr_horizInterface_flank0_isRCoast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_horizInterface_flank0_isRCoast_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x y : ℤ}
-- given
  (hbd : bdEdge (bcd_leftReach ω n) s(![x, y], ![x + 1, y]))
  (hqR : (![x + 1, y] : Site 2) ∈ bac_rightComplement ω n)
  (hp : (![x, y] : Site 2) ∈ rect 0 n 0 n)
  (hq : (![x + 1, y] : Site 2) ∈ rect 0 n 0 n) :
-- imply
  bac_IsRCoastFace ω n ![x, y] := by
-- proof
  apply StatMech.Universality.crr_horizInterface_flank0_isRCoast ω n hbd hqR hp hq

/--
[crr_horizInterface_flank1_isRCoast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_horizInterface_flank1_isRCoast_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x y : ℤ}
-- given
  (hbd : bdEdge (bcd_leftReach ω n) s(![x, y], ![x + 1, y]))
  (hqR : (![x + 1, y] : Site 2) ∈ bac_rightComplement ω n)
  (hp : (![x, y] : Site 2) ∈ rect 0 n 0 n)
  (hq : (![x + 1, y] : Site 2) ∈ rect 0 n 0 n) :
-- imply
  bac_IsRCoastFace ω n ![x, y - 1] := by
-- proof
  apply StatMech.Universality.crr_horizInterface_flank1_isRCoast ω n hbd hqR hp hq

/--
[crr_face_nbr_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_face_nbr_cases_eq
  {a b : ℤ}
  {g : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj ![a, b] g) :
-- imply
  g = ![a + 1, b] ∨ g = ![a - 1, b] ∨ g = ![a, b + 1] ∨ g = ![a, b - 1] := by
-- proof
  apply StatMech.Universality.crr_face_nbr_cases a b g hadj

/--
[crr_face_barrier_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_face_barrier_side_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n a b : ℤ}
-- given
  (h : ∃ g : Site 2, (pmd_boxFaceBarrier ω n).Adj ![a, b] g) :
-- imply
  ∃ u v : Site 2, ((u = ![a, b] ∧ v = ![a + 1, b]) ∨ (u = ![a, b + 1] ∧ v = ![a + 1, b + 1]) ∨ (u = ![a, b] ∧ v = ![a, b + 1]) ∨ (u = ![a + 1, b] ∧ v = ![a + 1, b + 1])) ∧ bdEdge (bcd_leftReach ω n) s(u, v) ∧ u ∈ rect 0 n 0 n ∧ v ∈ rect 0 n 0 n := by
-- proof
  apply StatMech.Universality.crr_face_barrier_side ω n a b h

/--
[crr_nbr_of_rCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_nbr_of_rCorner_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c c' : Site 2}
-- given
  (hc : c ∈ bac_rightComplement ω n)
  (hadj : (hypercubicLattice 2).Adj c c')
  (hc'box : c' ∈ rect 0 n 0 n) :
-- imply
  c' ∈ bcd_leftReach ω n ∨ c' ∈ bac_rightComplement ω n := by
-- proof
  apply StatMech.Universality.crr_nbr_of_rCorner ω n hc hadj hc'box

/--
[crr_corner_adj_or_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_corner_adj_or_diag_eq
  {a b : ℤ}
  {p q : Site 2}
-- given
  (hp : p = ![a, b] ∨ p = ![a + 1, b] ∨ p = ![a, b + 1] ∨ p = ![a + 1, b + 1])
  (hq : q = ![a, b] ∨ q = ![a + 1, b] ∨ q = ![a, b + 1] ∨ q = ![a + 1, b + 1])
  (hne : p ≠ q) :
-- imply
  (hypercubicLattice 2).Adj p q ∨ (p 0 ≠ q 0 ∧ p 1 ≠ q 1) := by
-- proof
  apply StatMech.Universality.crr_corner_adj_or_diag hp hq hne

/--
[crr_rCoastFace_has_interface_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_rCoastFace_has_interface_side_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {f : Site 2}
-- given
  (hf : bac_IsRCoastFace ω n f) :
-- imply
  crr_HasInterfaceSide ω n f := by
-- proof
  apply StatMech.Universality.crr_rCoastFace_has_interface_side ω n hf

/--
[crr_hasInterfaceSide_pmdVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_hasInterfaceSide_pmdVertex_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {f : Site 2}
-- given
  (h : crr_HasInterfaceSide ω n f) :
-- imply
  ∃ g : Site 2, (pmd_boxFaceBarrier ω n).Adj f g := by
-- proof
  apply StatMech.Universality.crr_hasInterfaceSide_pmdVertex ω n h

/--
[crr_hasInterfaceSide_of_with](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_hasInterfaceSide_of_with_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {f q : Site 2}
-- given
  (h : crr_InterfaceSideWith ω n f q) :
-- imply
  crr_HasInterfaceSide ω n f := by
-- proof
  apply StatMech.Universality.crr_hasInterfaceSide_of_with ω n h

/--
[crr_rCoastFace_interfaceSideWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_rCoastFace_interfaceSideWith_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {f : Site 2}
-- given
  (hf : bac_IsRCoastFace ω n f) :
-- imply
  ∃ q : Site 2, crr_InterfaceSideWith ω n f q := by
-- proof
  apply StatMech.Universality.crr_rCoastFace_interfaceSideWith ω n hf

/--
[crr_frontierFace_interfaceSideWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_frontierFace_interfaceSideWith_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {c₀ : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hc₀ : mbc_IsRightFrontier ω n c₀ 0) :
-- imply
  crr_InterfaceSideWith ω n ![c₀, 0] ![c₀ + 1, 0] := by
-- proof
  apply StatMech.Universality.crr_frontierFace_interfaceSideWith ω n hn hnoH hc₀

/--
[crr_rCoastConnected_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_rCoastConnected_of_residue_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hres : crr_InterfaceCoastConnected ω n) :
-- imply
  bac_RCoastConnected ω n := by
-- proof
  apply StatMech.Universality.crr_rCoastConnected_of_residue ω n hn hnoH hres

/--
[crr_frontierArcReaches_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_frontierArcReaches_of_residue_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hres : crr_InterfaceCoastConnected ω n) :
-- imply
  crc2_FrontierArcReaches ω n := by
-- proof
  apply StatMech.Universality.crr_frontierArcReaches_of_residue ω n hn hnoH hres

/--
[crr_faceDualVCrossing_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_faceDualVCrossing_of_residue_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hres : crr_InterfaceCoastConnected ω n) :
-- imply
  pmd_FaceDualVCrossing ω n := by
-- proof
  apply StatMech.Universality.crr_faceDualVCrossing_of_residue ω n hn hnoH hres

/--
[crr_reachesBottom_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_reachesBottom_of_residue_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hres : crr_InterfaceCoastConnected ω n) :
-- imply
  ccc_FrontierReachesBottom ω n := by
-- proof
  apply StatMech.Universality.crr_reachesBottom_of_residue ω n hn hnoH hres

/--
[crr_exhaustivity_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_exhaustivity_of_residue_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hres : crr_InterfaceCoastConnected ω n) :
-- imply
  HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n := by
-- proof
  apply StatMech.Universality.crr_exhaustivity_of_residue ω n hn hnoH hres

/--
[crr_residue_of_rCoastConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_residue_of_rCoastConnected_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hres : bac_RCoastConnected ω n) :
-- imply
  crr_InterfaceCoastConnected ω n := by
-- proof
  apply StatMech.Universality.crr_residue_of_rCoastConnected ω n hn hnoH hres

/--
[crr_wall_interfaceCoastConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_wall_interfaceCoastConnected_eq :
-- imply
  crr_InterfaceCoastConnected bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.crr_wall_interfaceCoastConnected

/--
[crr_wall_frontierArcReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_wall_frontierArcReaches_eq :
-- imply
  crc2_FrontierArcReaches bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.crr_wall_frontierArcReaches

/--
[crr_wall_rCoastConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_wall_rCoastConnected_eq :
-- imply
  bac_RCoastConnected bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.crr_wall_rCoastConnected

/--
[crr_wall_faceDualVCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_wall_faceDualVCrossing_eq :
-- imply
  pmd_FaceDualVCrossing bcc_wallCfg 2 := by
-- proof
  apply StatMech.Universality.crr_wall_faceDualVCrossing

/--
[crr_wall_noH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_wall_noH_eq :
-- imply
  ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 := by
-- proof
  apply StatMech.Universality.crr_wall_noH

/--
[crr_leftReach_openWalk_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_leftReach_openWalk_lift_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {u v : rect 0 n 0 n}
  {w : (openSubgraphInduce 2 omega (rect 0 n 0 n)).Walk u v}
-- given
  (hu : (u : Site 2) ∈ bcd_leftReach omega n) :
-- imply
  ∃ hv : (v : Site 2) ∈ bcd_leftReach omega n, ((hypercubicLattice 2).induce (bcd_leftReach omega n)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Universality.crr_leftReach_openWalk_lift omega n hu w

/--
[crr_leftWall_reaches_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_leftWall_reaches_zero_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n r : Int}
-- given
  (hr0 : 0 ≤ r)
  (hrn : r ≤ n) :
-- imply
  ∃ (hr : (![0, r] : Site 2) ∈ bcd_leftReach omega n) (h0 : (![0, 0] : Site 2) ∈ bcd_leftReach omega n), ((hypercubicLattice 2).induce (bcd_leftReach omega n)).Reachable ⟨![0, r], hr⟩ ⟨![0, 0], h0⟩ := by
-- proof
  apply StatMech.Universality.crr_leftWall_reaches_zero omega n r hr0 hrn

/--
[crr_leftReach_connected_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_leftReach_connected_pair_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {u v : Site 2}
-- given
  (hu : u ∈ bcd_leftReach omega n)
  (hv : v ∈ bcd_leftReach omega n) :
-- imply
  ((hypercubicLattice 2).induce (bcd_leftReach omega n)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Universality.crr_leftReach_connected_pair omega n hu hv

/--
[crr_leftWall_reaches_boxVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_leftWall_reaches_boxVertex_eq
  {n : Int}
  {u : Site 2}
-- given
  (hu : u ∈ rect 0 n 0 n) :
-- imply
  ∃ hl : (![0, u 1] : Site 2) ∈ rect 0 n 0 n, ((hypercubicLattice 2).induce (rect 0 n 0 n)).Reachable ⟨![0, u 1], hl⟩ ⟨u, hu⟩ := by
-- proof
  apply StatMech.Universality.crr_leftWall_reaches_boxVertex n hu

/--
[crr_walk_exit_set_in_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_walk_exit_set_in_box_eq
  {A B : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hw : ∀ z ∈ w.support, z ∈ B)
  (hx : x ∈ A)
  (hy : y ∉ A) :
-- imply
  ∃ a b : Site 2, (hypercubicLattice 2).Adj a b ∧ a ∈ A ∧ b ∉ A ∧ a ∈ B ∧ b ∈ B := by
-- proof
  apply StatMech.Universality.crr_walk_exit_set_in_box A B w hw hx hy

/--
[crr_rightComplement_of_boxMinusL_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_rightComplement_of_boxMinusL_reachable_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {u v : Site 2}
-- given
  (hu : u ∈ bac_boxMinusL omega n)
  (hv : v ∈ bac_boxMinusL omega n)
  (huv : ((hypercubicLattice 2).induce (bac_boxMinusL omega n)).Reachable ⟨u, hu⟩ ⟨v, hv⟩)
  (hvR : v ∈ bac_rightComplement omega n) :
-- imply
  u ∈ bac_rightComplement omega n := by
-- proof
  apply StatMech.Universality.crr_rightComplement_of_boxMinusL_reachable omega n hu hv huv hvR

/--
[crr_leftFill_reaches_leftReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_leftFill_reaches_leftReach_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {u : Site 2}
-- given
  (hu : u ∈ crr_leftFill omega n) :
-- imply
  ∃ z : Site 2, ∃ hzL : z ∈ bcd_leftReach omega n, ((hypercubicLattice 2).induce (crr_leftFill omega n)).Reachable ⟨u, hu⟩ ⟨z, ⟨bcd_leftReach_subset_box omega n hzL, fun hzR => (bac_rightComplement_mem omega n hzR).2 hzL⟩⟩ := by
-- proof
  apply StatMech.Universality.crr_leftFill_reaches_leftReach omega n hu

/--
[crr_leftFill_connected_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_leftFill_connected_pair_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {u v : Site 2}
-- given
  (hu : u ∈ crr_leftFill omega n)
  (hv : v ∈ crr_leftFill omega n) :
-- imply
  ((hypercubicLattice 2).induce (crr_leftFill omega n)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Universality.crr_leftFill_connected_pair omega n hu hv

/--
[crr_rightComplement_connected_induced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_rightComplement_connected_induced_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {u v : Site 2}
-- given
  (hnoH : ¬ HorizontalCrossing omega 0 n 0 n)
  (hu : u ∈ bac_rightComplement omega n)
  (hv : v ∈ bac_rightComplement omega n) :
-- imply
  ((hypercubicLattice 2).induce (bac_rightComplement omega n)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Universality.crr_rightComplement_connected_induced omega n hnoH hu hv

/--
[crr_boxRColour_sidesConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_boxRColour_sidesConnected_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
-- given
  (hnoH : ¬ HorizontalCrossing omega 0 n 0 n) :
-- imply
  Ising.kwg_ColourSidesConnected (crr_boxPlanar n).G (crr_boxRColour omega n) := by
-- proof
  apply StatMech.Universality.crr_boxRColour_sidesConnected omega n hnoH

/--
[crr_boxR_dualEven_subset_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_boxR_dualEven_subset_eq_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {F : Finset (Ising.kwg_Edge (crr_boxPlanar n))}
-- given
  (hnoH : ¬ HorizontalCrossing omega 0 n 0 n)
  (hsub : F ⊆ Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n)) (crr_boxRColour omega n))
  (hne : F.Nonempty)
  (heven : Ising.kwg_IsEven (Ising.kwg_dualEnds (crr_boxPlanar n)) F) :
-- imply
  F = Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n)) (crr_boxRColour omega n) := by
-- proof
  apply StatMech.Universality.crr_boxR_dualEven_subset_eq omega n hnoH F hsub hne heven

/--
[crr_faceAdj_isBoxInterior_of_mem_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_faceAdj_isBoxInterior_of_mem_interior_eq
  {n : Int}
  {f g : Site 2}
-- given
  (hf : f ∈ rect 0 (n - 1) 0 (n - 1))
  (hfg : (hypercubicLattice 2).Adj f g) :
-- imply
  crc2_IsBoxInteriorEdge n f g := by
-- proof
  apply StatMech.Universality.crr_faceAdj_isBoxInterior_of_mem_interior hf hfg

/--
[crr_LRFaceGraph_degree_eq_faceBoundary_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_LRFaceGraph_degree_eq_faceBoundary_degree_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {f : Site 2}
-- given
  (hf : f ∈ rect 0 (n - 1) 0 (n - 1)) :
-- imply
  (crr_LRFaceGraph omega n).degree f = (faceBoundaryGraph (bac_rightComplement omega n)).degree f := by
-- proof
  apply StatMech.Universality.crr_LRFaceGraph_degree_eq_faceBoundary_degree omega n hf

/--
[crr_LRFaceGraph_degree_even_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_LRFaceGraph_degree_even_of_interior_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {f : Site 2}
-- given
  (hf : f ∈ rect 0 (n - 1) 0 (n - 1)) :
-- imply
  Even ((crr_LRFaceGraph omega n).degree f) := by
-- proof
  apply StatMech.Universality.crr_LRFaceGraph_degree_even_of_interior omega n hf

/--
[crr_LRFaceGraph_adj_of_shared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_LRFaceGraph_adj_of_shared_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {f g p q : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hshared : sharedPrimalEdge f g = s(p, q))
  (hpL : p ∈ bcd_leftReach omega n)
  (hqR : q ∈ bac_rightComplement omega n)
  (hpbox : p ∈ rect 0 n 0 n)
  (hqbox : q ∈ rect 0 n 0 n) :
-- imply
  (crr_LRFaceGraph omega n).Adj f g := by
-- proof
  apply StatMech.Universality.crr_LRFaceGraph_adj_of_shared omega n hfg hshared hpL hqR hpbox hqbox

/--
[crr_interfaceSideWith_LRNeighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_interfaceSideWith_LRNeighbor_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {f q : Site 2}
-- given
  (h : crr_InterfaceSideWith omega n f q) :
-- imply
  ∃ g : Site 2, (crr_LRFaceGraph omega n).Adj f g := by
-- proof
  apply StatMech.Universality.crr_interfaceSideWith_LRNeighbor omega n h

/--
[crr_cutEdge_flanks_LRAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_cutEdge_flanks_LRAdj_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {e : Ising.kwg_Edge (crr_boxPlanar n)}
-- given
  (he : e ∈ Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n)) (crr_boxRColour omega n)) :
-- imply
  (crr_LRFaceGraph omega n).Adj (Ising.kwg_flankLeft (crr_boxPlanar n) e) (Ising.kwg_flankRight (crr_boxPlanar n) e) := by
-- proof
  apply StatMech.Universality.crr_cutEdge_flanks_LRAdj omega n e he

/--
[crr_mem_LRComponentEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_mem_LRComponentEdges_iff_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {f : Site 2}
  {e : Ising.kwg_Edge (crr_boxPlanar n)} :
-- imply
  e ∈ crr_LRComponentEdges omega n f ↔ e ∈ Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n)) (crr_boxRColour omega n) ∧ (crr_LRFaceGraph omega n).Reachable f (Ising.kwg_flankLeft (crr_boxPlanar n) e) := by
-- proof
  apply StatMech.Universality.crr_mem_LRComponentEdges_iff omega n f e

/--
[crr_boxImage_edge_endpoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_boxImage_edge_endpoint_mem_eq
  {n : Int}
  {e : Sym2 (Site 2)}
  {z : Site 2}
-- given
  (he : e ∈ (imageGraph (crr_boxPlanar n)).edgeSet)
  (hz : z ∈ e) :
-- imply
  z ∈ rect 0 n 0 n := by
-- proof
  apply StatMech.Universality.crr_boxImage_edge_endpoint_mem he hz

/--
[crr_face_interior_or_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_face_interior_or_frame_eq
  {n : Int}
  {f g : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (h : crc2_IsBoxInteriorEdge n f g) :
-- imply
  f ∈ rect 0 (n - 1) 0 (n - 1) ∨ f 0 = -1 ∨ f 0 = n ∨ f 1 = -1 ∨ f 1 = n := by
-- proof
  apply StatMech.Universality.crr_face_interior_or_frame hfg h

/--
[crr_boxEdge_one_flank_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_boxEdge_one_flank_interior_eq
  {n : Int}
  {f g : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (h : crc2_IsBoxInteriorEdge n f g) :
-- imply
  f ∈ rect 0 (n - 1) 0 (n - 1) ∨ g ∈ rect 0 (n - 1) 0 (n - 1) := by
-- proof
  apply StatMech.Universality.crr_boxEdge_one_flank_interior hfg h

/--
[crr_whb_box_adj_leftLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_whb_box_adj_leftLine_eq
  {n : Int}
  {f g : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hf : f 0 = -1)
  (hg : g 0 = -1) :
-- imply
  (whb_faceRegion (imageGraph (crr_boxPlanar n))).Adj f g := by
-- proof
  apply StatMech.Universality.crr_whb_box_adj_leftLine hfg hf hg

/--
[crr_whb_box_adj_rightLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_whb_box_adj_rightLine_eq
  {n : Int}
  {f g : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hf : f 0 = n)
  (hg : g 0 = n) :
-- imply
  (whb_faceRegion (imageGraph (crr_boxPlanar n))).Adj f g := by
-- proof
  apply StatMech.Universality.crr_whb_box_adj_rightLine hfg hf hg

/--
[crr_whb_box_adj_bottomLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_whb_box_adj_bottomLine_eq
  {n : Int}
  {f g : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hf : f 1 = -1)
  (hg : g 1 = -1) :
-- imply
  (whb_faceRegion (imageGraph (crr_boxPlanar n))).Adj f g := by
-- proof
  apply StatMech.Universality.crr_whb_box_adj_bottomLine hfg hf hg

/--
[crr_whb_box_adj_topLine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_whb_box_adj_topLine_eq
  {n : Int}
  {f g : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hf : f 1 = n)
  (hg : g 1 = n) :
-- imply
  (whb_faceRegion (imageGraph (crr_boxPlanar n))).Adj f g := by
-- proof
  apply StatMech.Universality.crr_whb_box_adj_topLine hfg hf hg

/--
[crr_frame_reachable_outerBeacon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_frame_reachable_outerBeacon_eq
  {n : Int}
  {f : Site 2}
-- given
  (hf : f 0 = -1 ∨ f 0 = n ∨ f 1 = -1 ∨ f 1 = n) :
-- imply
  (whb_faceRegion (imageGraph (crr_boxPlanar n))).Reachable f ![-1, -1] := by
-- proof
  apply StatMech.Universality.crr_frame_reachable_outerBeacon n hf

/--
[crr_sharedEdge_mem_boxImage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_sharedEdge_mem_boxImage_eq
  {n : Int}
  {f g p q : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hshared : sharedPrimalEdge f g = s(p, q))
  (hp : p ∈ rect 0 n 0 n)
  (hq : q ∈ rect 0 n 0 n) :
-- imply
  sharedPrimalEdge f g ∈ (imageGraph (crr_boxPlanar n)).edgeSet := by
-- proof
  apply StatMech.Universality.crr_sharedEdge_mem_boxImage hfg hshared hp hq

/--
[crr_whb_box_interior_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_whb_box_interior_isolated_eq
  {n : Int}
  {f g : Site 2}
-- given
  (hf : f ∈ rect 0 (n - 1) 0 (n - 1)) :
-- imply
  ¬ (whb_faceRegion (imageGraph (crr_boxPlanar n))).Adj f g := by
-- proof
  apply StatMech.Universality.crr_whb_box_interior_isolated hf

/--
[crr_whb_box_component_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_whb_box_component_singleton_eq
  {n : Int}
  {f g : Site 2}
-- given
  (hf : f ∈ rect 0 (n - 1) 0 (n - 1))
  (hcomp : (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk f = (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk g) :
-- imply
  f = g := by
-- proof
  apply StatMech.Universality.crr_whb_box_component_singleton hf hcomp

/--
[crr_nonOuter_flank_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_nonOuter_flank_interior_eq
  {n : Int}
  {e : Ising.kwg_Edge (crr_boxPlanar n)}
  {f : Site 2}
-- given
  (hf : f = Ising.kwg_flankLeft (crr_boxPlanar n) e ∨ f = Ising.kwg_flankRight (crr_boxPlanar n) e)
  (houter : (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk f ≠ (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk ![-1, -1]) :
-- imply
  f ∈ rect 0 (n - 1) 0 (n - 1) := by
-- proof
  apply StatMech.Universality.crr_nonOuter_flank_interior e hf houter

/--
[crr_LRAdj_exists_cutEdge_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_LRAdj_exists_cutEdge_incident_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {f g : Site 2}
-- given
  (hfint : f ∈ rect 0 (n - 1) 0 (n - 1))
  (hfg : (crr_LRFaceGraph omega n).Adj f g) :
-- imply
  ∃ e : Ising.kwg_Edge (crr_boxPlanar n), e ∈ Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n)) (crr_boxRColour omega n) ∧ Ising.kwg_incidentMod2 ((whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk f) (Ising.kwg_dualEnds (crr_boxPlanar n) e) := by
-- proof
  apply StatMech.Universality.crr_LRAdj_exists_cutEdge_incident omega n hfint hfg

/--
[crr_LRAdj_has_interior_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_LRAdj_has_interior_endpoint_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {f g : Site 2}
-- given
  (hfg : (crr_LRFaceGraph omega n).Adj f g) :
-- imply
  f ∈ rect 0 (n - 1) 0 (n - 1) ∨ g ∈ rect 0 (n - 1) 0 (n - 1) := by
-- proof
  apply StatMech.Universality.crr_LRAdj_has_interior_endpoint hfg

/--
[crr_boxFaceRep_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_boxFaceRep_component_eq
  {n : Int}
  {C : Ising.kwg_Face (crr_boxPlanar n)} :
-- imply
  (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk (crr_boxFaceRep n C) = C := by
-- proof
  apply StatMech.Universality.crr_boxFaceRep_component n C

/--
[crr_interfaceSide_reaches_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_interfaceSide_reaches_interior_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {f q : Site 2}
-- given
  (h : crr_InterfaceSideWith omega n f q) :
-- imply
  ∃ f' : Site 2, f' ∈ rect 0 (n - 1) 0 (n - 1) ∧ (crr_LRFaceGraph omega n).Reachable f f' ∧ ∃ g, (crr_LRFaceGraph omega n).Adj f' g := by
-- proof
  apply StatMech.Universality.crr_interfaceSide_reaches_interior omega n h

/--
[crr_interior_LRFaceGraph_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_interior_LRFaceGraph_reachable_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {f₁ f₂ : Site 2}
-- given
  (hnoH : ¬ HorizontalCrossing omega 0 n 0 n)
  (hf₁ : f₁ ∈ rect 0 (n - 1) 0 (n - 1))
  (hf₂ : f₂ ∈ rect 0 (n - 1) 0 (n - 1))
  (hinc₁ : ∃ g, (crr_LRFaceGraph omega n).Adj f₁ g)
  (hinc₂ : ∃ g, (crr_LRFaceGraph omega n).Adj f₂ g) :
-- imply
  (crr_LRFaceGraph omega n).Reachable f₁ f₂ := by
-- proof
  apply StatMech.Universality.crr_interior_LRFaceGraph_reachable omega n hnoH hf₁ hf₂ hinc₁ hinc₂

/--
[crr_leftFill_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_leftFill_finite_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  (crr_leftFill ω n).Finite := by
-- proof
  apply StatMech.Universality.crr_leftFill_finite ω n

/--
[crr_leftFill_bdEdge_is_leftReach_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_leftFill_bdEdge_is_leftReach_bdEdge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {p q : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj p q)
  (hpbox : p ∈ rect 0 n 0 n)
  (hqbox : q ∈ rect 0 n 0 n)
  (hbd : bdEdge (crr_leftFill ω n) s(p, q)) :
-- imply
  bdEdge (bcd_leftReach ω n) s(p, q) := by
-- proof
  apply StatMech.Universality.crr_leftFill_bdEdge_is_leftReach_bdEdge ω n hadj hpbox hqbox hbd

/--
[crr_leftFill_faceBoundary_inBox_pmd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_leftFill_faceBoundary_inBox_pmd_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {f g p q : Site 2}
-- given
  (hfg : (faceBoundaryGraph (crr_leftFill ω n)).Adj f g)
  (hshared : sharedPrimalEdge f g = s(p, q))
  (hpbox : p ∈ rect 0 n 0 n)
  (hqbox : q ∈ rect 0 n 0 n) :
-- imply
  (pmd_boxFaceBarrier ω n).Adj f g := by
-- proof
  apply StatMech.Universality.crr_leftFill_faceBoundary_inBox_pmd ω n hfg hshared hpbox hqbox

/--
[crr_LRFaceGraph_adj_leftFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_LRFaceGraph_adj_leftFill_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
  {f g : Site 2}
-- given
  (h : (crr_LRFaceGraph omega n).Adj f g) :
-- imply
  (faceBoundaryGraph (crr_leftFill omega n)).Adj f g := by
-- proof
  apply StatMech.Universality.crr_LRFaceGraph_adj_leftFill omega n h

/--
[crr_LRFaceGraph_le_pmd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_LRFaceGraph_le_pmd_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int} :
-- imply
  crr_LRFaceGraph omega n ≤ pmd_boxFaceBarrier omega n := by
-- proof
  apply StatMech.Universality.crr_LRFaceGraph_le_pmd omega n

/--
[crr_leftFill_walk_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_leftFill_walk_lift_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {u v : Site 2}
  {w : (faceBoundaryGraph (crr_leftFill ω n)).Walk u v}
-- given
  (hint : ∀ f g : Site 2, s(f, g) ∈ w.edges → crc2_IsBoxInteriorEdge n f g) :
-- imply
  (pmd_boxFaceBarrier ω n).Reachable u v := by
-- proof
  apply StatMech.Universality.crr_leftFill_walk_lift ω n w hint

/--
[crr_closedBoundary_select_complementaryArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_closedBoundary_select_complementaryArc_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {f₁ f₂ : Site 2}
  {c : (faceBoundaryGraph (crr_leftFill ω n)).Walk f₁ f₁}
-- given
  (hf₂ : f₂ ∈ c.support)
  (hside : (∀ f g : Site 2, s(f, g) ∈ (c.takeUntil f₂ hf₂).edges → crc2_IsBoxInteriorEdge n f g) ∨ (∀ f g : Site 2, s(f, g) ∈ (c.dropUntil f₂ hf₂).edges → crc2_IsBoxInteriorEdge n f g)) :
-- imply
  ∃ w : (faceBoundaryGraph (crr_leftFill ω n)).Walk f₁ f₂, ∀ f g : Site 2, s(f, g) ∈ w.edges → crc2_IsBoxInteriorEdge n f g := by
-- proof
  apply StatMech.Universality.crr_closedBoundary_select_complementaryArc ω n c hf₂ hside

/--
[crr_leftFillInteriorArc_of_frameArcOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_leftFillInteriorArc_of_frameArcOrder_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (horder : crr_LeftFillFrameArcOrder ω n) :
-- imply
  crr_LeftFillInteriorArc ω n := by
-- proof
  apply StatMech.Universality.crr_leftFillInteriorArc_of_frameArcOrder ω n horder

/--
[crr_interfaceCoastConnected_of_leftFillInteriorArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_interfaceCoastConnected_of_leftFillInteriorArc_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (harc : crr_LeftFillInteriorArc ω n) :
-- imply
  crr_InterfaceCoastConnected ω n := by
-- proof
  apply StatMech.Universality.crr_interfaceCoastConnected_of_leftFillInteriorArc ω n harc

/--
[crr_interfaceCoastConnected_of_frameArcOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_interfaceCoastConnected_of_frameArcOrder_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (horder : crr_LeftFillFrameArcOrder ω n) :
-- imply
  crr_InterfaceCoastConnected ω n := by
-- proof
  apply StatMech.Universality.crr_interfaceCoastConnected_of_frameArcOrder ω n horder

/--
[crr_leftFillInteriorArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_leftFillInteriorArc_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
-- given
  (hnoH : ¬ HorizontalCrossing omega 0 n 0 n) :
-- imply
  crr_LeftFillInteriorArc omega n := by
-- proof
  apply StatMech.Universality.crr_leftFillInteriorArc omega n hnoH

/--
[crr_leftFillFrameArcOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_leftFillFrameArcOrder_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
-- given
  (hnoH : ¬ HorizontalCrossing omega 0 n 0 n) :
-- imply
  crr_LeftFillFrameArcOrder omega n := by
-- proof
  apply StatMech.Universality.crr_leftFillFrameArcOrder omega n hnoH

/--
[crr_interfaceCoastConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_interfaceCoastConnected_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Int}
-- given
  (hnoH : ¬ HorizontalCrossing omega 0 n 0 n) :
-- imply
  crr_InterfaceCoastConnected omega n := by
-- proof
  apply StatMech.Universality.crr_interfaceCoastConnected omega n hnoH

/--
[crr_barrierConnectsRows_of_leftFillInteriorArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_barrierConnectsRows_of_leftFillInteriorArc_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (harc : crr_LeftFillInteriorArc ω n) :
-- imply
  pmd_BarrierConnectsRows ω n := by
-- proof
  apply StatMech.Universality.crr_barrierConnectsRows_of_leftFillInteriorArc ω n hn hnoH harc

/--
[crr_barrierConnectsRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_barrierConnectsRows_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  pmd_BarrierConnectsRows ω n := by
-- proof
  apply StatMech.Universality.crr_barrierConnectsRows ω n hn hnoH

/--
[crr_barrierFace_mem_faceRect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_barrierFace_mem_faceRect_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n a b : ℤ}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (h : ∃ g : Site 2, (pmd_boxFaceBarrier ω n).Adj ![a, b] g) :
-- imply
  (![a, b] : Site 2) ∈ rect 0 (n - 1) (-1) n := by
-- proof
  apply StatMech.Universality.crr_barrierFace_mem_faceRect ω n a b hnoH h

/--
[crr_verticalCrossing_of_barrierConnectsRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_verticalCrossing_of_barrierConnectsRows_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hrows : pmd_BarrierConnectsRows ω n) :
-- imply
  VerticalCrossing (fci_faceDualConfig ω) 0 (n - 1) (-1) n := by
-- proof
  apply StatMech.Universality.crr_verticalCrossing_of_barrierConnectsRows ω n hnoH hrows

/--
[crr_horizontalCrossing_faceBand_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_horizontalCrossing_faceBand_subset_eq
  {n : ℤ}
-- given
  (hn : 0 < n) :
-- imply
  horizontalCrossingEvent 0 (n + 1) 0 (n - 1) ⊆ horizontalCrossingEvent 0 (n + 1) 0 n := by
-- proof
  apply StatMech.Universality.crr_horizontalCrossing_faceBand_subset n hn

/--
[crr_faceDualRect_half_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_faceDualRect_half_law_eq
  {n : ℤ}
-- given
  (hmeas : MeasurableSet (crr_FaceRectVerticalEvent n)) :
-- imply
  rba_selfDualMeasure.real (crr_FaceDualRectEvent n) = rba_selfDualMeasure.real (crr_FaceRectVerticalEvent n) := by
-- proof
  apply StatMech.Universality.crr_faceDualRect_half_law n hmeas

/--
[crr_faceRectVertical_real_le_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_faceRectVertical_real_le_square_eq
  {n : ℤ}
-- given
  (hn : 0 < n)
  (hmeasThin : MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
-- imply
  rba_selfDualMeasure.real (crr_FaceRectVerticalEvent n) ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.crr_faceRectVertical_real_le_square n hn hmeasThin

/--
[crr_square_compl_subset_faceDualRect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_square_compl_subset_faceDualRect_eq
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (horder : ∀ ω : ConfigSpace (Sym2 (Site 2)), crr_LeftFillFrameArcOrder ω n) :
-- imply
  (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ crr_FaceDualRectEvent n := by
-- proof
  apply StatMech.Universality.crr_square_compl_subset_faceDualRect n hn horder

/--
[crr_square_compl_subset_faceDualRect_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_square_compl_subset_faceDualRect_unconditional_eq
  {n : ℤ}
-- given
  (hn : 0 ≤ n) :
-- imply
  (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ crr_FaceDualRectEvent n := by
-- proof
  apply StatMech.Universality.crr_square_compl_subset_faceDualRect_unconditional n hn

/--
[crr_square_half_of_frameArcOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_square_half_of_frameArcOrder_eq
  {n : ℤ}
-- given
  (hn : 0 < n)
  (horder : ∀ ω : ConfigSpace (Sym2 (Site 2)), crr_LeftFillFrameArcOrder ω n)
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
  (hmeasFace : MeasurableSet (crr_FaceRectVerticalEvent n))
  (hmeasThin : MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.crr_square_half_of_frameArcOrder n hn horder hmeasH hmeasFace hmeasThin

/--
[crr_square_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_square_half_eq
  {n : ℤ}
-- given
  (hn : 0 < n)
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
  (hmeasFace : MeasurableSet (crr_FaceRectVerticalEvent n))
  (hmeasThin : MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.crr_square_half n hn hmeasH hmeasFace hmeasThin

/--
[crr_faceDualConnectionEvent_eq_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_faceDualConnectionEvent_eq_preimage_eq
  {n : ℤ} :
-- imply
  crr_FaceDualConnectionEvent n = fci_faceDualConfig ⁻¹' crr_FaceConnectionEvent n := by
-- proof
  apply StatMech.Universality.crr_faceDualConnectionEvent_eq_preimage n

/--
[crr_faceDualConnection_half_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_faceDualConnection_half_law_eq
  {n : ℤ}
-- given
  (hmeas : MeasurableSet (crr_FaceConnectionEvent n)) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one) (crr_FaceDualConnectionEvent n) = (bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one) (crr_FaceConnectionEvent n) := by
-- proof
  apply StatMech.Universality.crr_faceDualConnection_half_law n hmeas

/--
[crr_square_compl_subset_faceDualConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_square_compl_subset_faceDualConnection_eq
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (horder : ∀ ω : ConfigSpace (Sym2 (Site 2)), crr_LeftFillFrameArcOrder ω n) :
-- imply
  (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ crr_FaceDualConnectionEvent n := by
-- proof
  apply StatMech.Universality.crr_square_compl_subset_faceDualConnection n hn horder

/--
[crr_square_half_of_frameArcOrder_and_faceComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_square_half_of_frameArcOrder_and_faceComparison_eq
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (horder : ∀ ω : ConfigSpace (Sym2 (Site 2)), crr_LeftFillFrameArcOrder ω n)
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
  (hmeasFace : MeasurableSet (crr_FaceConnectionEvent n))
  (hcompare : (bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one).real (crr_FaceConnectionEvent n) ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one).real (horizontalCrossingEvent 0 n 0 n)) :
-- imply
  (1 : ℝ) / 2 ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one).real (horizontalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.crr_square_half_of_frameArcOrder_and_faceComparison n hn horder hmeasH hmeasFace hcompare

/--
[crr_faceDualVCrossing_of_leftFillInteriorArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_faceDualVCrossing_of_leftFillInteriorArc_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (harc : crr_LeftFillInteriorArc ω n) :
-- imply
  pmd_FaceDualVCrossing ω n := by
-- proof
  apply StatMech.Universality.crr_faceDualVCrossing_of_leftFillInteriorArc ω n hn hnoH harc

/--
[crr_wall_frameFace_not_pmd_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_wall_frameFace_not_pmd_support_eq :
-- imply
  (![2, 0] : Site 2) ∉ (pmd_boxFaceBarrier bcc_wallCfg 2).support := by
-- proof
  apply StatMech.Universality.crr_wall_frameFace_not_pmd_support

/--
[crr_wall_frameEdge_not_pmd_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean)
-/
@[path]
private lemma crr_wall_frameEdge_not_pmd_reachable_eq :
-- imply
  ¬ (pmd_boxFaceBarrier bcc_wallCfg 2).Reachable ![2, 0] ![2, -1] := by
-- proof
  apply StatMech.Universality.crr_wall_frameEdge_not_pmd_reachable


-- created on 2026-10-23
