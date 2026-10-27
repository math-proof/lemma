import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.earremovable.Part5
open Finset Set SimpleGraph Function StatMech StatMech.Walls


/--
[ear_exists_globalExtreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_exists_globalExtreme_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ c, ear_IsGlobalExtreme K c := by
-- proof
  apply StatMech.Walls.ear_exists_globalExtreme K hK hne

/--
[ear_globalExtreme_not_mem_of_higher](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_globalExtreme_not_mem_of_higher_eq
  {K : Set (Site 2)}
  {c v : Site 2}
-- given
  (hc : ear_IsGlobalExtreme K c)
  (hy : c 1 < v 1) :
-- imply
  v ∉ K := by
-- proof
  apply StatMech.Walls.ear_globalExtreme_not_mem_of_higher K c v hc hy

/--
[ear_globalExtreme_not_mem_of_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_globalExtreme_not_mem_of_right_eq
  {K : Set (Site 2)}
  {c v : Site 2}
-- given
  (hc : ear_IsGlobalExtreme K c)
  (hy : v 1 = c 1)
  (hx : c 0 < v 0) :
-- imply
  v ∉ K := by
-- proof
  apply StatMech.Walls.ear_globalExtreme_not_mem_of_right K c v hc hy hx

/--
[ear_globalExtreme_up_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_globalExtreme_up_nmem_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : ear_IsGlobalExtreme K c) :
-- imply
  c + ![0, 1] ∉ K := by
-- proof
  apply StatMech.Walls.ear_globalExtreme_up_nmem K c hc

/--
[ear_globalExtreme_right_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_globalExtreme_right_nmem_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : ear_IsGlobalExtreme K c) :
-- imply
  c + ![1, 0] ∉ K := by
-- proof
  apply StatMech.Walls.ear_globalExtreme_right_nmem K c hc

/--
[ear_globalExtreme_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_globalExtreme_boundary_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hc : ear_IsGlobalExtreme K c) :
-- imply
  ∃ n ∉ K, (hypercubicLattice 2).Adj c n := by
-- proof
  apply StatMech.Walls.ear_globalExtreme_boundary K c hc

/--
[ear_globalExtreme_neighbor_left_or_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_globalExtreme_neighbor_left_or_down_eq
  {K : Set (Site 2)}
  {c v : Site 2}
-- given
  (hc : ear_IsGlobalExtreme K c)
  (hv : v ∈ K)
  (hadj : (hypercubicLattice 2).Adj v c) :
-- imply
  v = c + ![-1, 0] ∨ v = c + ![0, -1] := by
-- proof
  apply StatMech.Walls.ear_globalExtreme_neighbor_left_or_down K c v hc hv hadj

/--
[ear_adj_leftCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_adj_leftCell_eq
  {c : Site 2} :
-- imply
  (hypercubicLattice 2).Adj c (ear_leftCell c) := by
-- proof
  apply StatMech.Walls.ear_adj_leftCell c

/--
[ear_adj_downCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_adj_downCell_eq
  {c : Site 2} :
-- imply
  (hypercubicLattice 2).Adj c (ear_downCell c) := by
-- proof
  apply StatMech.Walls.ear_adj_downCell c

/--
[ear_leftCell_ne_downCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_leftCell_ne_downCell_eq
  {c : Site 2} :
-- imply
  ear_leftCell c ≠ ear_downCell c := by
-- proof
  apply StatMech.Walls.ear_leftCell_ne_downCell c

/--
[ear_globalExtreme_neighbor_leftCell_or_downCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_globalExtreme_neighbor_leftCell_or_downCell_eq
  {K : Set (Site 2)}
  {c v : Site 2}
-- given
  (hc : ear_IsGlobalExtreme K c)
  (hv : v ∈ K)
  (hadj : (hypercubicLattice 2).Adj c v) :
-- imply
  v = ear_leftCell c ∨ v = ear_downCell c := by
-- proof
  apply StatMech.Walls.ear_globalExtreme_neighbor_leftCell_or_downCell K c v hc hv hadj

/--
[ear_exists_neighbor_of_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_exists_neighbor_of_conn_eq
  {K : Finset (Site 2)}
  {c : Site 2}
-- given
  (hcard : 2 ≤ K.card)
  (hconn : IsConnectedCluster K)
  (hc : c ∈ K) :
-- imply
  ∃ v ∈ K, (hypercubicLattice 2).Adj c v := by
-- proof
  apply StatMech.Walls.ear_exists_neighbor_of_conn hcard hconn hc

/--
[ear_globalExtreme_pendant_of_down_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_globalExtreme_pendant_of_down_nmem_eq
  {K : Finset (Site 2)}
  {c : Site 2}
-- given
  (hcard : 2 ≤ K.card)
  (hconn : IsConnectedCluster K)
  (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
  (hdown : ear_downCell c ∉ (↑K : Set (Site 2))) :
-- imply
  jc_IsPendantCell (↑K : Set (Site 2)) c := by
-- proof
  apply StatMech.Walls.ear_globalExtreme_pendant_of_down_nmem hcard hconn hc hdown

/--
[ear_globalExtreme_pendant_of_left_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_globalExtreme_pendant_of_left_nmem_eq
  {K : Finset (Site 2)}
  {c : Site 2}
-- given
  (hcard : 2 ≤ K.card)
  (hconn : IsConnectedCluster K)
  (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
  (hleft : ear_leftCell c ∉ (↑K : Set (Site 2))) :
-- imply
  jc_IsPendantCell (↑K : Set (Site 2)) c := by
-- proof
  apply StatMech.Walls.ear_globalExtreme_pendant_of_left_nmem hcard hconn hc hleft

/--
[ear_removable_of_pendant_ne_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_removable_of_pendant_ne_origin_eq
  {K : Finset (Site 2)}
  {c : Site 2}
-- given
  (hconn : IsConnectedCluster K)
  (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
  (hcorigin : c ≠ origin 2)
  (hpend : jc_IsPendantCell (↑K : Set (Site 2)) c) :
-- imply
  ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧ CellConnected ((↑K : Set (Site 2)) \ {d}) := by
-- proof
  apply StatMech.Walls.ear_removable_of_pendant_ne_origin hconn hc hcorigin hpend

/--
[ear_mem_vtromino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_mem_vtromino_eq
  {v : Site 2} :
-- imply
  v ∈ ear_vtromino ↔ v = ![0, 0] ∨ v = ![-1, 0] ∨ v = ![0, -1] := by
-- proof
  apply StatMech.Walls.ear_mem_vtromino v

/--
[ear_vt_v00](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_vt_v00_eq :
-- imply
  (![0, 0] : Site 2) ∈ ear_vtromino := by
-- proof
  apply StatMech.Walls.ear_vt_v00

/--
[ear_vt_vm10](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_vt_vm10_eq :
-- imply
  (![-1, 0] : Site 2) ∈ ear_vtromino := by
-- proof
  apply StatMech.Walls.ear_vt_vm10

/--
[ear_vt_v0m1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_vt_v0m1_eq :
-- imply
  (![0, -1] : Site 2) ∈ ear_vtromino := by
-- proof
  apply StatMech.Walls.ear_vt_v0m1

/--
[ear_vtromino_globalExtreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_vtromino_globalExtreme_eq :
-- imply
  ear_IsGlobalExtreme ear_vtromino ![0, 0] := by
-- proof
  apply StatMech.Walls.ear_vtromino_globalExtreme

/--
[ear_vtromino_two_neighbours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_vtromino_two_neighbours_eq :
-- imply
  ear_leftCell (![0, 0] : Site 2) ∈ ear_vtromino ∧ ear_downCell (![0, 0] : Site 2) ∈ ear_vtromino := by
-- proof
  apply StatMech.Walls.ear_vtromino_two_neighbours

/--
[ear_vtd_vm10](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_vtd_vm10_eq :
-- imply
  (![-1, 0] : Site 2) ∈ ear_vtromino \ {![0, 0]} := by
-- proof
  apply StatMech.Walls.ear_vtd_vm10

/--
[ear_vtd_v0m1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_vtd_v0m1_eq :
-- imply
  (![0, -1] : Site 2) ∈ ear_vtromino \ {![0, 0]} := by
-- proof
  apply StatMech.Walls.ear_vtd_v0m1

/--
[ear_vtromino_arm_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_vtromino_arm_isolated_eq :
-- imply
  ((hypercubicLattice 2).induce (ear_vtromino \ {![0, 0]})).neighborSet ⟨![-1, 0], ear_vtd_vm10⟩ = ∅ := by
-- proof
  apply StatMech.Walls.ear_vtromino_arm_isolated

/--
[ear_vtromino_arm_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_vtromino_arm_ne_eq :
-- imply
  (⟨![-1, 0], ear_vtd_vm10⟩ : ↑(ear_vtromino \ {![0, 0]})) ≠ ⟨![0, -1], ear_vtd_v0m1⟩ := by
-- proof
  apply StatMech.Walls.ear_vtromino_arm_ne

/--
[ear_vtromino_extreme_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_vtromino_extreme_cut_eq :
-- imply
  ¬ CellConnected (ear_vtromino \ {![0, 0]}) := by
-- proof
  apply StatMech.Walls.ear_vtromino_extreme_cut

/--
[ear_exists_antiExtreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_exists_antiExtreme_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ b, ear_IsAntiExtreme K b := by
-- proof
  apply StatMech.Walls.ear_exists_antiExtreme K hK hne

/--
[ear_antiExtreme_not_mem_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_antiExtreme_not_mem_of_lower_eq
  {K : Set (Site 2)}
  {b v : Site 2}
-- given
  (hb : ear_IsAntiExtreme K b)
  (hy : v 1 < b 1) :
-- imply
  v ∉ K := by
-- proof
  apply StatMech.Walls.ear_antiExtreme_not_mem_of_lower K b v hb hy

/--
[ear_antiExtreme_not_mem_of_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_antiExtreme_not_mem_of_left_eq
  {K : Set (Site 2)}
  {b v : Site 2}
-- given
  (hb : ear_IsAntiExtreme K b)
  (hy : v 1 = b 1)
  (hx : v 0 < b 0) :
-- imply
  v ∉ K := by
-- proof
  apply StatMech.Walls.ear_antiExtreme_not_mem_of_left K b v hb hy hx

/--
[ear_antiExtreme_down_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_antiExtreme_down_nmem_eq
  {K : Set (Site 2)}
  {b : Site 2}
-- given
  (hb : ear_IsAntiExtreme K b) :
-- imply
  b + ![0, -1] ∉ K := by
-- proof
  apply StatMech.Walls.ear_antiExtreme_down_nmem K b hb

/--
[ear_antiExtreme_left_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_antiExtreme_left_nmem_eq
  {K : Set (Site 2)}
  {b : Site 2}
-- given
  (hb : ear_IsAntiExtreme K b) :
-- imply
  b + ![-1, 0] ∉ K := by
-- proof
  apply StatMech.Walls.ear_antiExtreme_left_nmem K b hb

/--
[ear_antiExtreme_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_antiExtreme_boundary_eq
  {K : Set (Site 2)}
  {b : Site 2}
-- given
  (hb : ear_IsAntiExtreme K b) :
-- imply
  ∃ n ∉ K, (hypercubicLattice 2).Adj b n := by
-- proof
  apply StatMech.Walls.ear_antiExtreme_boundary K b hb

/--
[ear_adj_rightCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_adj_rightCell_eq
  {b : Site 2} :
-- imply
  (hypercubicLattice 2).Adj b (ear_rightCell b) := by
-- proof
  apply StatMech.Walls.ear_adj_rightCell b

/--
[ear_adj_upCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_adj_upCell_eq
  {b : Site 2} :
-- imply
  (hypercubicLattice 2).Adj b (ear_upCell b) := by
-- proof
  apply StatMech.Walls.ear_adj_upCell b

/--
[ear_antiExtreme_neighbor_rightCell_or_upCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_antiExtreme_neighbor_rightCell_or_upCell_eq
  {K : Set (Site 2)}
  {b v : Site 2}
-- given
  (hb : ear_IsAntiExtreme K b)
  (hv : v ∈ K)
  (hadj : (hypercubicLattice 2).Adj b v) :
-- imply
  v = ear_rightCell b ∨ v = ear_upCell b := by
-- proof
  apply StatMech.Walls.ear_antiExtreme_neighbor_rightCell_or_upCell K b v hb hv hadj

/--
[ear_antiExtreme_pendant_of_up_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_antiExtreme_pendant_of_up_nmem_eq
  {K : Finset (Site 2)}
  {b : Site 2}
-- given
  (hcard : 2 ≤ K.card)
  (hconn : IsConnectedCluster K)
  (hb : ear_IsAntiExtreme (↑K : Set (Site 2)) b)
  (hup : ear_upCell b ∉ (↑K : Set (Site 2))) :
-- imply
  jc_IsPendantCell (↑K : Set (Site 2)) b := by
-- proof
  apply StatMech.Walls.ear_antiExtreme_pendant_of_up_nmem hcard hconn hb hup

/--
[ear_antiExtreme_pendant_of_right_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_antiExtreme_pendant_of_right_nmem_eq
  {K : Finset (Site 2)}
  {b : Site 2}
-- given
  (hcard : 2 ≤ K.card)
  (hconn : IsConnectedCluster K)
  (hb : ear_IsAntiExtreme (↑K : Set (Site 2)) b)
  (hright : ear_rightCell b ∉ (↑K : Set (Site 2))) :
-- imply
  jc_IsPendantCell (↑K : Set (Site 2)) b := by
-- proof
  apply StatMech.Walls.ear_antiExtreme_pendant_of_right_nmem hcard hconn hb hright

/--
[ear_gKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_gKey_injective_eq :
-- imply
  Function.Injective ear_gKey := by
-- proof
  apply StatMech.Walls.ear_gKey_injective

/--
[ear_extremes_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_extremes_distinct_eq
  {K : Finset (Site 2)}
  {c b : Site 2}
-- given
  (hcard : 2 ≤ K.card)
  (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
  (hb : ear_IsAntiExtreme (↑K : Set (Site 2)) b) :
-- imply
  c ≠ b := by
-- proof
  apply StatMech.Walls.ear_extremes_distinct hcard hc hb

/--
[ear_removable_of_antiPendant_ne_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_removable_of_antiPendant_ne_origin_eq
  {K : Finset (Site 2)}
  {b : Site 2}
-- given
  (hconn : IsConnectedCluster K)
  (hb : ear_IsAntiExtreme (↑K : Set (Site 2)) b)
  (hborigin : b ≠ origin 2)
  (hpend : jc_IsPendantCell (↑K : Set (Site 2)) b) :
-- imply
  ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧ CellConnected ((↑K : Set (Site 2)) \ {d}) := by
-- proof
  apply StatMech.Walls.ear_removable_of_antiPendant_ne_origin hconn hb hborigin hpend

/--
[ear_globalExtreme_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_globalExtreme_dichotomy_eq
  {K : Finset (Site 2)}
  {c : Site 2}
-- given
  (hcard : 2 ≤ K.card)
  (hconn : IsConnectedCluster K)
  (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
  (hcorigin : c ≠ origin 2) :
-- imply
  (∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧ CellConnected ((↑K : Set (Site 2)) \ {d})) ∨ (ear_leftCell c ∈ (↑K : Set (Site 2)) ∧ ear_downCell c ∈ (↑K : Set (Site 2))) := by
-- proof
  apply StatMech.Walls.ear_globalExtreme_dichotomy hcard hconn hc hcorigin

/--
[ear_antiExtreme_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_antiExtreme_dichotomy_eq
  {K : Finset (Site 2)}
  {b : Site 2}
-- given
  (hcard : 2 ≤ K.card)
  (hconn : IsConnectedCluster K)
  (hb : ear_IsAntiExtreme (↑K : Set (Site 2)) b)
  (hborigin : b ≠ origin 2) :
-- imply
  (∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧ CellConnected ((↑K : Set (Site 2)) \ {d})) ∨ (ear_rightCell b ∈ (↑K : Set (Site 2)) ∧ ear_upCell b ∈ (↑K : Set (Site 2))) := by
-- proof
  apply StatMech.Walls.ear_antiExtreme_dichotomy hcard hconn hb hborigin

/--
[ear_boundaryNonCut_of_pendantExtreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_boundaryNonCut_of_pendantExtreme_eq
  {K : Finset (Site 2)}
-- given
  (_hcard : 2 ≤ K.card)
  (hconn : IsConnectedCluster K)
  (hpend : (∃ c, ear_IsGlobalExtreme (↑K : Set (Site 2)) c ∧ c ≠ origin 2 ∧ jc_IsPendantCell (↑K : Set (Site 2)) c) ∨ (∃ b, ear_IsAntiExtreme (↑K : Set (Site 2)) b ∧ b ≠ origin 2 ∧ jc_IsPendantCell (↑K : Set (Site 2)) b)) :
-- imply
  ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧ CellConnected ((↑K : Set (Site 2)) \ {d}) := by
-- proof
  apply StatMech.Walls.ear_boundaryNonCut_of_pendantExtreme _hcard hconn hpend

/--
[ear_cutWitness_globalExtreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_cutWitness_globalExtreme_eq :
-- imply
  ear_IsGlobalExtreme cutWitness ![2, 1] := by
-- proof
  apply StatMech.Walls.ear_cutWitness_globalExtreme

/--
[ear_cutWitness_globalExtreme_pendant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_cutWitness_globalExtreme_pendant_eq :
-- imply
  jc_IsPendantCell cutWitness ![2, 1] := by
-- proof
  apply StatMech.Walls.ear_cutWitness_globalExtreme_pendant

/--
[ear_cutWitness_removable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_cutWitness_removable_eq :
-- imply
  CellConnected (cutWitness \ {![2, 1]}) := by
-- proof
  apply StatMech.Walls.ear_cutWitness_removable

/--
[ear_tromino_globalExtreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_tromino_globalExtreme_eq :
-- imply
  ear_IsGlobalExtreme (↑pc2_tromino : Set (Site 2)) ![0, 1] := by
-- proof
  apply StatMech.Walls.ear_tromino_globalExtreme

/--
[ear_tromino_antiExtreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_tromino_antiExtreme_eq :
-- imply
  ear_IsAntiExtreme (↑pc2_tromino : Set (Site 2)) ![0, 0] := by
-- proof
  apply StatMech.Walls.ear_tromino_antiExtreme

/--
[ear_tromino_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean)
-/
@[path]
private lemma ear_tromino_nonvacuous_eq :
-- imply
  ∃ c ∈ pc2_tromino, c ≠ origin 2 ∧ (∃ n ∉ pc2_tromino, (hypercubicLattice 2).Adj c n) ∧ CellConnected ((↑pc2_tromino : Set (Site 2)) \ {c}) := by
-- proof
  apply StatMech.Walls.ear_tromino_nonvacuous


-- created on 2026-10-23
