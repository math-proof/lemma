import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzClose.Part5
open SimpleGraph Function Set StatMech StatMech.Lattice


/--
[uc_totalTurn_eq_four_of_winds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_totalTurn_eq_four_of_winds_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hmax : uc_WindsAtMostOnce K a)
  (hmin : uc_WindsAtLeastOnce K a) :
-- imply
  totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨ totalTurnZ K a.1 (dartOrbitPeriod K a) = -4 := by
-- proof
  apply StatMech.Lattice.uc_totalTurn_eq_four_of_winds K a hmax hmin

/--
[uc_winds_of_totalTurn_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_winds_of_totalTurn_eq_four_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨ totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) :
-- imply
  uc_WindsAtMostOnce K a ∧ uc_WindsAtLeastOnce K a := by
-- proof
  apply StatMech.Lattice.uc_winds_of_totalTurn_eq_four K a h

/--
[uc_winds_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_winds_iff_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (uc_WindsAtMostOnce K a ∧ uc_WindsAtLeastOnce K a) ↔ (totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨ totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) := by
-- proof
  apply StatMech.Lattice.uc_winds_iff K a

/--
[uc_turningIsFullRevolution_of_winds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_turningIsFullRevolution_of_winds_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hmax : uc_WindsAtMostOnce K a)
  (hmin : uc_WindsAtLeastOnce K a) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.uc_turningIsFullRevolution_of_winds K a hmax hmin

/--
[uc_base_totalTurn_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_base_totalTurn_eq_four_eq
  {v : Site 2}
  {a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}} :
-- imply
  totalTurnZ ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = 4 ∨ totalTurnZ ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = -4 := by
-- proof
  apply StatMech.Lattice.uc_base_totalTurn_eq_four v a

/--
[uc_step_preserves_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_step_preserves_turn_eq
  {K K' : Set (Site 2)}
  {e e' : Dart}
  {m m' n : ℕ}
-- given
  (hmatch : ∀ i, i < n → turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
  (hbal : umEar_windowTurn K' e' 0 m' = umEar_windowTurn K e 0 m) :
-- imply
  totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) := by
-- proof
  apply StatMech.Lattice.uc_step_preserves_turn K K' e e' m m' n hmatch hbal

/--
[uc_turningIsFullRevolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_turningIsFullRevolution_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hsat : bpc_BalanceSaturatingContraction)
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.uc_turningIsFullRevolution hsat K hK hne a

/--
[uc_totalTurn_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_totalTurn_eq_four_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hsat : bpc_BalanceSaturatingContraction)
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨ totalTurnZ K a.1 (dartOrbitPeriod K a) = -4 := by
-- proof
  apply StatMech.Lattice.uc_totalTurn_eq_four hsat K hK hne a

/--
[uc_totalTurnAngle_eq_two_pi_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_totalTurnAngle_eq_two_pi_iff_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (totalTurnAngle K a.1 (dartOrbitPeriod K a) = 2 * Real.pi ∨ totalTurnAngle K a.1 (dartOrbitPeriod K a) = -(2 * Real.pi)) ↔ (totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨ totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) := by
-- proof
  apply StatMech.Lattice.uc_totalTurnAngle_eq_two_pi_iff K a

/--
[uc_totalTurnAngle_eq_two_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_totalTurnAngle_eq_two_pi_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hsat : bpc_BalanceSaturatingContraction)
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  totalTurnAngle K a.1 (dartOrbitPeriod K a) = 2 * Real.pi ∨ totalTurnAngle K a.1 (dartOrbitPeriod K a) = -(2 * Real.pi) := by
-- proof
  apply StatMech.Lattice.uc_totalTurnAngle_eq_two_pi hsat K hK hne a

/--
[uc_unitCell_totalTurn_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_unitCell_totalTurn_eq_four_eq :
-- imply
  totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 ∨ totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 := by
-- proof
  apply StatMech.Lattice.uc_unitCell_totalTurn_eq_four

/--
[uc_unitCell_totalTurnAngle_eq_two_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_unitCell_totalTurnAngle_eq_two_pi_eq :
-- imply
  totalTurnAngle unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 2 * Real.pi ∨ totalTurnAngle unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -(2 * Real.pi) := by
-- proof
  apply StatMech.Lattice.uc_unitCell_totalTurnAngle_eq_two_pi

/--
[uc_unitCell_winds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_unitCell_winds_eq :
-- imply
  uc_WindsAtMostOnce unitCell ucBase ∧ uc_WindsAtLeastOnce unitCell ucBase := by
-- proof
  apply StatMech.Lattice.uc_unitCell_winds

/--
[uc_domino_totalTurn_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_domino_totalTurn_eq_four_eq :
-- imply
  totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = 4 ∨ totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = -4 := by
-- proof
  apply StatMech.Lattice.uc_domino_totalTurn_eq_four

/--
[uc_domino_totalTurnAngle_eq_two_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_domino_totalTurnAngle_eq_two_pi_eq :
-- imply
  totalTurnAngle domino dmBase.1 (dartOrbitPeriod domino dmBase) = 2 * Real.pi ∨ totalTurnAngle domino dmBase.1 (dartOrbitPeriod domino dmBase) = -(2 * Real.pi) := by
-- proof
  apply StatMech.Lattice.uc_domino_totalTurnAngle_eq_two_pi

/--
[uc_domino_winds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_domino_winds_eq :
-- imply
  uc_WindsAtMostOnce domino dmBase ∧ uc_WindsAtLeastOnce domino dmBase := by
-- proof
  apply StatMech.Lattice.uc_domino_winds

/--
[uc_domino_saturating_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_domino_saturating_witness_eq :
-- imply
  ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty) (a' : {e : Dart // IsBoundaryDart K' e}), K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase := by
-- proof
  apply StatMech.Lattice.uc_domino_saturating_witness

/--
[uc_winds_iff_turningIsFullRevolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_winds_iff_turningIsFullRevolution_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (uc_WindsAtMostOnce K a ∧ uc_WindsAtLeastOnce K a) ↔ TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.uc_winds_iff_turningIsFullRevolution K a

/--
[uc_rot90Fun_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_rot90Fun_add_eq
  {x y : Site 2} :
-- imply
  rot90Fun (x + y) = rot90Fun x + rot90Fun y := by
-- proof
  apply StatMech.Lattice.uc_rot90Fun_add x y

/--
[uc_rotSet_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_rotSet_mem_iff_eq
  {K : Set (Site 2)}
  {z : Site 2} :
-- imply
  rot90Fun z ∈ uc_rotSet K ↔ z ∈ K := by
-- proof
  apply StatMech.Lattice.uc_rotSet_mem_iff K z

/--
[uc_rotDart_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_rotDart_tail_eq
  {e : Dart} :
-- imply
  (uc_rotDart e).tail = rot90Fun e.tail := by
-- proof
  apply StatMech.Lattice.uc_rotDart_tail e

/--
[uc_rotDart_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_rotDart_dir_eq
  {e : Dart} :
-- imply
  (uc_rotDart e).dir = rot90Fun e.dir := by
-- proof
  apply StatMech.Lattice.uc_rotDart_dir e

/--
[uc_rotDart_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_rotDart_head_eq
  {e : Dart} :
-- imply
  (uc_rotDart e).head = rot90Fun e.head := by
-- proof
  apply StatMech.Lattice.uc_rotDart_head e

/--
[uc_rotDart_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_rotDart_injective_eq :
-- imply
  Function.Injective uc_rotDart := by
-- proof
  apply StatMech.Lattice.uc_rotDart_injective

/--
[uc_turnZ_rot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_turnZ_rot_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  turnZ (uc_rotSet K) (uc_rotDart e) = turnZ K e := by
-- proof
  apply StatMech.Lattice.uc_turnZ_rot K e

/--
[uc_dartNext_rot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_dartNext_rot_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  dartNext (uc_rotSet K) (uc_rotDart e) = uc_rotDart (dartNext K e) := by
-- proof
  apply StatMech.Lattice.uc_dartNext_rot K e

/--
[uc_iterate_dartNext_rot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_iterate_dartNext_rot_eq
  {K : Set (Site 2)}
  {e : Dart}
  {k : ℕ} :
-- imply
  (dartNext (uc_rotSet K))^[k] (uc_rotDart e) = uc_rotDart ((dartNext K)^[k] e) := by
-- proof
  apply StatMech.Lattice.uc_iterate_dartNext_rot K e k

/--
[uc_rotDart_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_rotDart_boundary_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e) :
-- imply
  IsBoundaryDart (uc_rotSet K) (uc_rotDart e) := by
-- proof
  apply StatMech.Lattice.uc_rotDart_boundary K e he

/--
[uc_rightCornerCount_rot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_rightCornerCount_rot_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ} :
-- imply
  rightCornerCount (uc_rotSet K) (uc_rotDart e) p = rightCornerCount K e p := by
-- proof
  apply StatMech.Lattice.uc_rightCornerCount_rot K e p

/--
[uc_leftCornerCount_rot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_leftCornerCount_rot_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ} :
-- imply
  leftCornerCount (uc_rotSet K) (uc_rotDart e) p = leftCornerCount K e p := by
-- proof
  apply StatMech.Lattice.uc_leftCornerCount_rot K e p

/--
[uc_rotSub_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_rotSub_val_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (uc_rotSub K a).1 = uc_rotDart a.1 := by
-- proof
  apply StatMech.Lattice.uc_rotSub_val K a

/--
[uc_isPeriodicPt_rot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_isPeriodicPt_rot_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {n : ℕ} :
-- imply
  Function.IsPeriodicPt (dartNextSub (uc_rotSet K)) n (uc_rotSub K a) ↔ Function.IsPeriodicPt (dartNextSub K) n a := by
-- proof
  apply StatMech.Lattice.uc_isPeriodicPt_rot K a n

/--
[uc_dartOrbitPeriod_rot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_dartOrbitPeriod_rot_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  dartOrbitPeriod (uc_rotSet K) (uc_rotSub K a) = dartOrbitPeriod K a := by
-- proof
  apply StatMech.Lattice.uc_dartOrbitPeriod_rot K a

/--
[uc_cornerBalance_rot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_cornerBalance_rot_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  cornerBalance (uc_rotSet K) (uc_rotSub K a) = cornerBalance K a := by
-- proof
  apply StatMech.Lattice.uc_cornerBalance_rot K a

/--
[uc_totalTurnZ_rot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_totalTurnZ_rot_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  totalTurnZ (uc_rotSet K) (uc_rotSub K a).1 (dartOrbitPeriod (uc_rotSet K) (uc_rotSub K a)) = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Lattice.uc_totalTurnZ_rot K a

/--
[uc_turningIsFullRevolution_rot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_turningIsFullRevolution_rot_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : TurningIsFullRevolution K a) :
-- imply
  TurningIsFullRevolution (uc_rotSet K) (uc_rotSub K a) := by
-- proof
  apply StatMech.Lattice.uc_turningIsFullRevolution_rot K a h

/--
[uc_rotSet_domino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_rotSet_domino_eq :
-- imply
  uc_rotSet domino = {![0, 0], ![0, 1]} := by
-- proof
  apply StatMech.Lattice.uc_rotSet_domino

/--
[uc_verticalDomino_totalTurn_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_verticalDomino_totalTurn_eq_four_eq :
-- imply
  totalTurnZ (uc_rotSet domino) (uc_rotSub domino dmBase).1 (dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase)) = 4 ∨ totalTurnZ (uc_rotSet domino) (uc_rotSub domino dmBase).1 (dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase)) = -4 := by
-- proof
  apply StatMech.Lattice.uc_verticalDomino_totalTurn_eq_four

/--
[uc_verticalDomino_totalTurnAngle_eq_two_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_verticalDomino_totalTurnAngle_eq_two_pi_eq :
-- imply
  totalTurnAngle (uc_rotSet domino) (uc_rotSub domino dmBase).1 (dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase)) = 2 * Real.pi ∨ totalTurnAngle (uc_rotSet domino) (uc_rotSub domino dmBase).1 (dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase)) = -(2 * Real.pi) := by
-- proof
  apply StatMech.Lattice.uc_verticalDomino_totalTurnAngle_eq_two_pi

/--
[uc_generalFullRevolution_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_generalFullRevolution_of_saturating_eq
-- given
  (hsat : bpc_BalanceSaturatingContraction) :
-- imply
  uc_GeneralFullRevolution := by
-- proof
  apply StatMech.Lattice.uc_generalFullRevolution_of_saturating hsat

/--
[uc_generalEulerCharOne_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_generalEulerCharOne_of_saturating_eq
-- given
  (hsat : bpc_BalanceSaturatingContraction) :
-- imply
  uc_GeneralEulerCharOne := by
-- proof
  apply StatMech.Lattice.uc_generalEulerCharOne_of_saturating hsat

/--
[uc_fullRevolution_of_eulerCharOne_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_fullRevolution_of_eulerCharOne_period_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (h : EulerCharOne K a) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.uc_fullRevolution_of_eulerCharOne_period K a hp h

/--
[uc_verticalDomino_eulerCharOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean)
-/
@[path]
private lemma uc_verticalDomino_eulerCharOne_eq :
-- imply
  EulerCharOne (uc_rotSet domino) (uc_rotSub domino dmBase) := by
-- proof
  apply StatMech.Lattice.uc_verticalDomino_eulerCharOne


-- created on 2026-10-23
