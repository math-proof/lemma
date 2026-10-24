import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.wstsigntoggle
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[wst_prefixSum_telescope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_prefixSum_telescope_eq
  {ind : ℕ → ℤ} :
-- imply
  ∀ n : ℕ, ((List.range n).map (fun i => ind (i + 1) - ind i)).sum = ind n - ind 0 := by
-- proof
  apply StatMech.Lattice.wst_prefixSum_telescope ind

/--
[wst_prefixSums_in_01_of_indicatorSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_prefixSums_in_01_of_indicatorSteps_eq
  {ind : ℕ → ℤ}
  {n : ℕ}
-- given
  (h01 : ∀ n, ind n = 0 ∨ ind n = 1)
  (h0 : ind 0 = 0) :
-- imply
  ∀ p ∈ wna_prefixSums ((List.range n).map (fun i => ind (i + 1) - ind i)), p = 0 ∨ p = 1 := by
-- proof
  apply StatMech.Lattice.wst_prefixSums_in_01_of_indicatorSteps ind h01 h0 n

/--
[wst_prefixSums_in_01_of_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_prefixSums_in_01_of_toggle_eq
  {L : List ℤ}
  {ind : ℕ → ℤ}
-- given
  (h01 : ∀ n, ind n = 0 ∨ ind n = 1)
  (h0 : ind 0 = 0)
  (hL : L = (List.range L.length).map (fun i => ind (i + 1) - ind i)) :
-- imply
  ∀ p ∈ wna_prefixSums L, p = 0 ∨ p = 1 := by
-- proof
  apply StatMech.Lattice.wst_prefixSums_in_01_of_toggle L ind h01 h0 hL

/--
[wst_alt_of_indicatorSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_alt_of_indicatorSteps_eq
  {L : List ℤ}
  {ind : ℕ → ℤ}
-- given
  (hpm : ∀ x ∈ L, x = 1 ∨ x = -1)
  (h01 : ∀ n, ind n = 0 ∨ ind n = 1)
  (h0 : ind 0 = 0)
  (hL : L = (List.range L.length).map (fun i => ind (i + 1) - ind i)) :
-- imply
  wnu_Alt L := by
-- proof
  apply StatMech.Lattice.wst_alt_of_indicatorSteps L ind hpm h01 h0 hL

/--
[wst_alt_map_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_alt_map_neg_eq :
-- imply
  ∀ L : List ℤ, wnu_Alt L → wnu_Alt (L.map (fun x => -x)) := by
-- proof
  apply StatMech.Lattice.wst_alt_map_neg

/--
[wst_alt_of_prefixSums_in_0neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_alt_of_prefixSums_in_0neg_eq
  {L : List ℤ}
-- given
  (hpm : ∀ x ∈ L, x = 1 ∨ x = -1)
  (hpref : ∀ p ∈ wna_prefixSums L, p = 0 ∨ p = -1) :
-- imply
  wnu_Alt L := by
-- proof
  apply StatMech.Lattice.wst_alt_of_prefixSums_in_0neg L hpm hpref

/--
[wst_alt_of_indicatorSteps_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_alt_of_indicatorSteps_neg_eq
  {L : List ℤ}
  {ind : ℕ → ℤ}
-- given
  (hpm : ∀ x ∈ L, x = 1 ∨ x = -1)
  (h0neg : ∀ n, ind n = 0 ∨ ind n = -1)
  (h0 : ind 0 = 0)
  (hL : L = (List.range L.length).map (fun i => ind (i + 1) - ind i)) :
-- imply
  wnu_Alt L := by
-- proof
  apply StatMech.Lattice.wst_alt_of_indicatorSteps_neg L ind hpm h0neg h0 hL

/--
[wst_columnAlternates_of_indicatorSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_columnAlternates_of_indicatorSteps_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : wst_IndicatorSteps z w) :
-- imply
  wna_ColumnAlternates z w := by
-- proof
  apply StatMech.Lattice.wst_columnAlternates_of_indicatorSteps z w h

/--
[wst_signedCrossPMone_of_indicatorSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_signedCrossPMone_of_indicatorSteps_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hK : K.Finite)
  (hstep : wst_IndicatorSteps z (olb_orbitLoop K hK a.1 a.2))
  (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2))) :
-- imply
  wnd_SignedCrossPMone K hK a z := by
-- proof
  apply StatMech.Lattice.wst_signedCrossPMone_of_indicatorSteps K hK a z hstep hodd

/--
[wst_revCount_pm_one_of_indicatorSteps_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_revCount_pm_one_of_indicatorSteps_bridge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hK : K.Finite)
  (hstep : wst_IndicatorSteps z (olb_orbitLoop K hK a.1 a.2))
  (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
  (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
-- imply
  revCount K a = 1 ∨ revCount K a = -1 := by
-- proof
  apply StatMech.Lattice.wst_revCount_pm_one_of_indicatorSteps_bridge K hK a z hstep hodd hbridge

/--
[wst_eulerCharOne_of_indicatorSteps_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_eulerCharOne_of_indicatorSteps_bridge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hK : K.Finite)
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hstep : wst_IndicatorSteps z (olb_orbitLoop K hK a.1 a.2))
  (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
  (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
-- imply
  EulerCharOne K a := by
-- proof
  apply StatMech.Lattice.wst_eulerCharOne_of_indicatorSteps_bridge K hK a z hp hstep hodd hbridge

/--
[wst_unitSquare_indicatorSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_unitSquare_indicatorSteps_eq :
-- imply
  wst_IndicatorSteps (![1, 1] : Site 2) wwit_unitSquareLoop := by
-- proof
  apply StatMech.Lattice.wst_unitSquare_indicatorSteps

/--
[wst_Ltromino_indicatorSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_Ltromino_indicatorSteps_eq :
-- imply
  wst_IndicatorSteps (![1, 1] : Site 2) wnu_LtrominoLoop := by
-- proof
  apply StatMech.Lattice.wst_Ltromino_indicatorSteps

/--
[wst_unitSquare_columnAlternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_unitSquare_columnAlternates_eq :
-- imply
  wna_ColumnAlternates (![1, 1] : Site 2) wwit_unitSquareLoop := by
-- proof
  apply StatMech.Lattice.wst_unitSquare_columnAlternates

/--
[wst_Ltromino_columnAlternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_Ltromino_columnAlternates_eq :
-- imply
  wna_ColumnAlternates (![1, 1] : Site 2) wnu_LtrominoLoop := by
-- proof
  apply StatMech.Lattice.wst_Ltromino_columnAlternates

/--
[wst_doubleSquare_not_indicatorSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_doubleSquare_not_indicatorSteps_eq :
-- imply
  ¬ wst_IndicatorSteps (![1, 1] : Site 2) wnu_doubleSquare := by
-- proof
  apply StatMech.Lattice.wst_doubleSquare_not_indicatorSteps

/--
[wst_doubleSquare_prefix_leaves_twoState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wstsigntoggle.lean)
-/
@[path]
private lemma wst_doubleSquare_prefix_leaves_twoState_eq :
-- imply
  ∃ p ∈ wna_prefixSums [(1 : ℤ), 1], ¬ (p = 0 ∨ p = 1) ∧ ¬ (p = 0 ∨ p = -1) := by
-- proof
  apply StatMech.Lattice.wst_doubleSquare_prefix_leaves_twoState


-- created on 2026-10-23
