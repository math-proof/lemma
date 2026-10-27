import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[wnu_Alt_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_Alt_nil_eq :
-- imply
  wnu_Alt [] := by
-- proof
  apply StatMech.Lattice.wnu_Alt_nil

/--
[wnu_Alt_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_Alt_singleton_eq
  {a : ℤ} :
-- imply
  wnu_Alt [a] ↔ (a = 1 ∨ a = -1) := by
-- proof
  apply StatMech.Lattice.wnu_Alt_singleton a

/--
[wnu_Alt_cons_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_Alt_cons_cons_eq
  {a b : ℤ}
  {t : List ℤ} :
-- imply
  wnu_Alt (a :: b :: t) ↔ (a = 1 ∨ a = -1) ∧ b = -a ∧ wnu_Alt (b :: t) := by
-- proof
  apply StatMech.Lattice.wnu_Alt_cons_cons

/--
[wnu_Alt_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_Alt_tail_eq
  {a : ℤ}
  {t : List ℤ}
-- given
  (h : wnu_Alt (a :: t)) :
-- imply
  wnu_Alt t := by
-- proof
  apply StatMech.Lattice.wnu_Alt_tail h

/--
[wnu_Alt_head_pm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_Alt_head_pm_eq
  {a : ℤ}
  {t : List ℤ}
-- given
  (h : wnu_Alt (a :: t)) :
-- imply
  a = 1 ∨ a = -1 := by
-- proof
  apply StatMech.Lattice.wnu_Alt_head_pm h

/--
[wnu_altSum_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_altSum_mem_eq :
-- imply
  ∀ (L : List ℤ), wnu_Alt L → (L.sum = 0 ∨ (∃ s, (s = 1 ∨ s = -1) ∧ L.sum = s)) := by
-- proof
  apply StatMech.Lattice.wnu_altSum_mem

/--
[wnu_altSum_abs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_altSum_abs_le_one_eq
  {L : List ℤ}
-- given
  (h : wnu_Alt L) :
-- imply
  |L.sum| ≤ 1 := by
-- proof
  apply StatMech.Lattice.wnu_altSum_abs_le_one L h

/--
[wnu_altSum_pm_one_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_altSum_pm_one_of_ne_zero_eq
  {L : List ℤ}
-- given
  (h : wnu_Alt L)
  (hne : L.sum ≠ 0) :
-- imply
  L.sum = 1 ∨ L.sum = -1 := by
-- proof
  apply StatMech.Lattice.wnu_altSum_pm_one_of_ne_zero L h hne

/--
[wnu_sum_filter_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_sum_filter_ne_zero_eq
  {L : List ℤ} :
-- imply
  L.sum = (L.filter (fun s => s ≠ 0)).sum := by
-- proof
  apply StatMech.Lattice.wnu_sum_filter_ne_zero L

/--
[wnu_signedCross_eq_filter_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_signedCross_eq_filter_sum_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  wnd_signedCross z w = ((w.darts.map (fun d => wnd_signStep z d.toProd.1 d.toProd.2)).filter (fun s => s ≠ 0)).sum := by
-- proof
  apply StatMech.Lattice.wnu_signedCross_eq_filter_sum z w

/--
[wnu_signedList_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_signedList_sum_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  (wnu_signedList z w).sum = wnd_signedCross z w := by
-- proof
  apply StatMech.Lattice.wnu_signedList_sum z w

/--
[wnu_signedCross_abs_le_one_of_alternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_signedCross_abs_le_one_of_alternates_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (halt : wnu_Alternates z w) :
-- imply
  |wnd_signedCross z w| ≤ 1 := by
-- proof
  apply StatMech.Lattice.wnu_signedCross_abs_le_one_of_alternates z w halt

/--
[wnu_signedCross_pm_one_of_alternates_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_signedCross_pm_one_of_alternates_of_ne_zero_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (halt : wnu_Alternates z w)
  (hne : wnd_signedCross z w ≠ 0) :
-- imply
  wnd_signedCross z w = 1 ∨ wnd_signedCross z w = -1 := by
-- proof
  apply StatMech.Lattice.wnu_signedCross_pm_one_of_alternates_of_ne_zero z w halt hne

/--
[wnu_signedCross_pm_one_of_alternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_signedCross_pm_one_of_alternates_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (halt : wnu_Alternates z w)
  (hodd : ¬ Even (jec_rayCount z w)) :
-- imply
  wnd_signedCross z w = 1 ∨ wnd_signedCross z w = -1 := by
-- proof
  apply StatMech.Lattice.wnu_signedCross_pm_one_of_alternates z w halt hodd

/--
[wnu_signedCrossPMone_of_alternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_signedCrossPMone_of_alternates_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hK : K.Finite)
  (halt : wnu_Alternates z (olb_orbitLoop K hK a.1 a.2))
  (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2))) :
-- imply
  wnd_SignedCrossPMone K hK a z := by
-- proof
  apply StatMech.Lattice.wnu_signedCrossPMone_of_alternates K hK a z halt hodd

/--
[wnu_revCount_pm_one_of_alternates_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_revCount_pm_one_of_alternates_bridge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hK : K.Finite)
  (halt : wnu_Alternates z (olb_orbitLoop K hK a.1 a.2))
  (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
  (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
-- imply
  revCount K a = 1 ∨ revCount K a = -1 := by
-- proof
  apply StatMech.Lattice.wnu_revCount_pm_one_of_alternates_bridge K hK a z halt hodd hbridge

/--
[wnu_eulerCharOne_of_alternates_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_eulerCharOne_of_alternates_bridge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hK : K.Finite)
  (hp : 3 ≤ dartOrbitPeriod K a)
  (halt : wnu_Alternates z (olb_orbitLoop K hK a.1 a.2))
  (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
  (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
-- imply
  EulerCharOne K a := by
-- proof
  apply StatMech.Lattice.wnu_eulerCharOne_of_alternates_bridge K hK a z hp halt hodd hbridge

/--
[wnu_not_alt_oneOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_not_alt_oneOne_eq :
-- imply
  ¬ wnu_Alt [1, 1] := by
-- proof
  apply StatMech.Lattice.wnu_not_alt_oneOne

/--
[wnu_unitSquare_signedList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_unitSquare_signedList_eq :
-- imply
  wnu_signedList (![1, 1] : Site 2) wwit_unitSquareLoop = [1] := by
-- proof
  apply StatMech.Lattice.wnu_unitSquare_signedList

/--
[wnu_unitSquare_alternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_unitSquare_alternates_eq :
-- imply
  wnu_Alternates (![1, 1] : Site 2) wwit_unitSquareLoop := by
-- proof
  apply StatMech.Lattice.wnu_unitSquare_alternates

/--
[wnu_unitSquare_signedCross_abs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_unitSquare_signedCross_abs_le_one_eq :
-- imply
  |wnd_signedCross (![1, 1] : Site 2) wwit_unitSquareLoop| ≤ 1 := by
-- proof
  apply StatMech.Lattice.wnu_unitSquare_signedCross_abs_le_one

/--
[wnu_doubleSquare_signedList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_doubleSquare_signedList_eq :
-- imply
  wnu_signedList (![1, 1] : Site 2) wnu_doubleSquare = [1, 1] := by
-- proof
  apply StatMech.Lattice.wnu_doubleSquare_signedList

/--
[wnu_doubleSquare_not_alternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_doubleSquare_not_alternates_eq :
-- imply
  ¬ wnu_Alternates (![1, 1] : Site 2) wnu_doubleSquare := by
-- proof
  apply StatMech.Lattice.wnu_doubleSquare_not_alternates

/--
[wnu_doubleSquare_signedCross_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_doubleSquare_signedCross_two_eq :
-- imply
  wnd_signedCross (![1, 1] : Site 2) wnu_doubleSquare = 2 := by
-- proof
  apply StatMech.Lattice.wnu_doubleSquare_signedCross_two

/--
[wnu_doubleSquare_not_pm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_doubleSquare_not_pm_one_eq :
-- imply
  ¬ (wnd_signedCross (![1, 1] : Site 2) wnu_doubleSquare = 1 ∨ wnd_signedCross (![1, 1] : Site 2) wnu_doubleSquare = -1) := by
-- proof
  apply StatMech.Lattice.wnu_doubleSquare_not_pm_one

/--
[wnu_Ltromino_signedList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_Ltromino_signedList_eq :
-- imply
  wnu_signedList (![1, 1] : Site 2) wnu_LtrominoLoop = [-1] := by
-- proof
  apply StatMech.Lattice.wnu_Ltromino_signedList

/--
[wnu_Ltromino_alternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_Ltromino_alternates_eq :
-- imply
  wnu_Alternates (![1, 1] : Site 2) wnu_LtrominoLoop := by
-- proof
  apply StatMech.Lattice.wnu_Ltromino_alternates

/--
[wnu_Ltromino_signedCross_abs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean)
-/
@[path]
private lemma wnu_Ltromino_signedCross_abs_le_one_eq :
-- imply
  |wnd_signedCross (![1, 1] : Site 2) wnu_LtrominoLoop| ≤ 1 := by
-- proof
  apply StatMech.Lattice.wnu_Ltromino_signedCross_abs_le_one


-- created on 2026-10-23
