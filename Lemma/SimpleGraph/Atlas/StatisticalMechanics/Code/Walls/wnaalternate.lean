import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[wna_altSum_abs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_altSum_abs_le_one_eq
  {L : List ℤ}
-- given
  (h : wnu_Alt L) :
-- imply
  |L.sum| ≤ 1 := by
-- proof
  apply StatMech.Lattice.wna_altSum_abs_le_one L h

/--
[wna_alt_of_prefix_in_01](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_alt_of_prefix_in_01_eq :
-- imply
  ∀ (L : List ℤ) (s : ℤ), (s = 0 ∨ s = 1) → (∀ x ∈ L, x = 1 ∨ x = -1) → (∀ p ∈ (L.scanl (· + ·) s), p = 0 ∨ p = 1) → wnu_Alt L := by
-- proof
  apply StatMech.Lattice.wna_alt_of_prefix_in_01

/--
[wna_alt_of_prefixSums_in_01](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_alt_of_prefixSums_in_01_eq
  {L : List ℤ}
-- given
  (hpm : ∀ x ∈ L, x = 1 ∨ x = -1)
  (hpref : ∀ p ∈ wna_prefixSums L, p = 0 ∨ p = 1) :
-- imply
  wnu_Alt L := by
-- proof
  apply StatMech.Lattice.wna_alt_of_prefixSums_in_01 L hpm hpref

/--
[wna_signedCross_abs_le_one_of_columnAlternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_signedCross_abs_le_one_of_columnAlternates_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : wna_ColumnAlternates z w) :
-- imply
  |wnd_signedCross z w| ≤ 1 := by
-- proof
  apply StatMech.Lattice.wna_signedCross_abs_le_one_of_columnAlternates z w h

/--
[wna_signedCross_pm_one_of_columnAlternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_signedCross_pm_one_of_columnAlternates_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : wna_ColumnAlternates z w)
  (hodd : ¬ Even (jec_rayCount z w)) :
-- imply
  wnd_signedCross z w = 1 ∨ wnd_signedCross z w = -1 := by
-- proof
  apply StatMech.Lattice.wna_signedCross_pm_one_of_columnAlternates z w h hodd

/--
[wna_alternates_of_signedList_alt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_alternates_of_signedList_alt_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : wnu_Alt (wnu_signedList z w)) :
-- imply
  wnu_Alternates z w := by
-- proof
  apply StatMech.Lattice.wna_alternates_of_signedList_alt z w h

/--
[wna_alternates_of_columnAlternates_id](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_alternates_of_columnAlternates_id_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : wnu_Alt (wnu_signedList z w)) :
-- imply
  wna_ColumnAlternates z w := by
-- proof
  apply StatMech.Lattice.wna_alternates_of_columnAlternates_id z w h

/--
[wna_unitSquare_columnAlternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_unitSquare_columnAlternates_eq :
-- imply
  wna_ColumnAlternates (![1, 1] : Site 2) wwit_unitSquareLoop := by
-- proof
  apply StatMech.Lattice.wna_unitSquare_columnAlternates

/--
[wna_unitSquare_signedCross_abs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_unitSquare_signedCross_abs_le_one_eq :
-- imply
  |wnd_signedCross (![1, 1] : Site 2) wwit_unitSquareLoop| ≤ 1 := by
-- proof
  apply StatMech.Lattice.wna_unitSquare_signedCross_abs_le_one

/--
[wna_Ltromino_columnAlternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_Ltromino_columnAlternates_eq :
-- imply
  wna_ColumnAlternates (![1, 1] : Site 2) wnu_LtrominoLoop := by
-- proof
  apply StatMech.Lattice.wna_Ltromino_columnAlternates

/--
[wna_Ltromino_signedCross_abs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_Ltromino_signedCross_abs_le_one_eq :
-- imply
  |wnd_signedCross (![1, 1] : Site 2) wnu_LtrominoLoop| ≤ 1 := by
-- proof
  apply StatMech.Lattice.wna_Ltromino_signedCross_abs_le_one

/--
[wna_toggle_on_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_toggle_on_singleton_eq :
-- imply
  wnu_Alt [(1 : ℤ)] := by
-- proof
  apply StatMech.Lattice.wna_toggle_on_singleton

/--
[wna_doubleSquare_not_columnAlternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_doubleSquare_not_columnAlternates_eq :
-- imply
  ¬ wna_ColumnAlternates (![1, 1] : Site 2) wnu_doubleSquare := by
-- proof
  apply StatMech.Lattice.wna_doubleSquare_not_columnAlternates

/--
[wna_doubleSquare_prefix_leaves_01](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_doubleSquare_prefix_leaves_01_eq :
-- imply
  ∃ p ∈ wna_prefixSums [(1 : ℤ), 1], ¬ (p = 0 ∨ p = 1) := by
-- proof
  apply StatMech.Lattice.wna_doubleSquare_prefix_leaves_01

/--
[wna_signedCrossPMone_of_columnAlternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_signedCrossPMone_of_columnAlternates_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hK : K.Finite)
  (halt : wna_ColumnAlternates z (olb_orbitLoop K hK a.1 a.2))
  (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2))) :
-- imply
  wnd_SignedCrossPMone K hK a z := by
-- proof
  apply StatMech.Lattice.wna_signedCrossPMone_of_columnAlternates K hK a z halt hodd

/--
[wna_revCount_pm_one_of_columnAlternates_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_revCount_pm_one_of_columnAlternates_bridge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hK : K.Finite)
  (halt : wna_ColumnAlternates z (olb_orbitLoop K hK a.1 a.2))
  (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
  (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
-- imply
  revCount K a = 1 ∨ revCount K a = -1 := by
-- proof
  apply StatMech.Lattice.wna_revCount_pm_one_of_columnAlternates_bridge K hK a z halt hodd hbridge

/--
[wna_eulerCharOne_of_columnAlternates_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean)
-/
@[path]
private lemma wna_eulerCharOne_of_columnAlternates_bridge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hK : K.Finite)
  (hp : 3 ≤ dartOrbitPeriod K a)
  (halt : wna_ColumnAlternates z (olb_orbitLoop K hK a.1 a.2))
  (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
  (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
-- imply
  EulerCharOne K a := by
-- proof
  apply StatMech.Lattice.wna_eulerCharOne_of_columnAlternates_bridge K hK a z hp halt hodd hbridge


-- created on 2026-10-23
