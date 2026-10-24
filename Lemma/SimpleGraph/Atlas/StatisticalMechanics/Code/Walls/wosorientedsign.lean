import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.wosorientedsign
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[wos_signsAlternate_columnAlternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_signsAlternate_columnAlternates_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : wos_SignsAlternateInColumnOrder z w) :
-- imply
  wna_ColumnAlternates z w := by
-- proof
  apply StatMech.Lattice.wos_signsAlternate_columnAlternates z w h

/--
[wos_signedCross_abs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_signedCross_abs_le_one_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : wos_SignsAlternateInColumnOrder z w) :
-- imply
  |wnd_signedCross z w| ≤ 1 := by
-- proof
  apply StatMech.Lattice.wos_signedCross_abs_le_one z w h

/--
[wos_signedCross_pm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_signedCross_pm_one_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : wos_SignsAlternateInColumnOrder z w)
  (hodd : ¬ Even (jec_rayCount z w)) :
-- imply
  wnd_signedCross z w = 1 ∨ wnd_signedCross z w = -1 := by
-- proof
  apply StatMech.Lattice.wos_signedCross_pm_one z w h hodd

/--
[wos_alt_eq_of_len_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_alt_eq_of_len_head_eq
  {L M : List ℤ}
-- given
  (hL : wnu_Alt L)
  (hM : wnu_Alt M)
  (hlen : L.length = M.length)
  (hhead : L.headI = M.headI) :
-- imply
  L = M := by
-- proof
  apply StatMech.Lattice.wos_alt_eq_of_len_head hL hM hlen hhead

/--
[wos_alt_map_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_alt_map_neg_eq
  {L : List ℤ}
-- given
  (h : wnu_Alt L) :
-- imply
  wnu_Alt (L.map (fun x => -x)) := by
-- proof
  apply StatMech.Lattice.wos_alt_map_neg h

/--
[wos_nonzeroDiffs_head_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_nonzeroDiffs_head_one_eq
  {f : ℕ → ℤ}
  {n : ℕ}
-- given
  (h01 : ∀ n, f n = 0 ∨ f n = 1)
  (h0 : f 0 = 0)
  (hne : wis_nonzeroDiffs f n ≠ []) :
-- imply
  (wis_nonzeroDiffs f n).headI = 1 := by
-- proof
  apply StatMech.Lattice.wos_nonzeroDiffs_head_one f h01 h0 n hne

/--
[wos_indNonzeroDiffs_alternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_indNonzeroDiffs_alternates_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c₀ : ℤ}
  {N : ℕ}
-- given
  (hbase : wis_indSeq z Vc c₀ 0 = 0) :
-- imply
  wnu_Alt (wis_nonzeroDiffs (wis_indSeq z Vc c₀) N) := by
-- proof
  apply StatMech.Lattice.wos_indNonzeroDiffs_alternates z Vc c₀ N hbase

/--
[wos_nonzeroDiffs_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_nonzeroDiffs_neg_eq
  {f : ℕ → ℤ}
  {n : ℕ} :
-- imply
  wis_nonzeroDiffs (fun i => - f i) n = (wis_nonzeroDiffs f n).map (fun x => -x) := by
-- proof
  apply StatMech.Lattice.wos_nonzeroDiffs_neg f n

/--
[wos_signEqIndicatorJumps_of_alternate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_signEqIndicatorJumps_of_alternate_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (halt : wos_SignsAlternateInColumnOrder z Vc)
  (hlen : wos_IndicatorLenEq z Vc) :
-- imply
  wis_SignEqIndicatorJumps z Vc := by
-- proof
  apply StatMech.Lattice.wos_signEqIndicatorJumps_of_alternate z Vc halt hlen

/--
[wos_unitSquare_signsAlternate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_unitSquare_signsAlternate_eq :
-- imply
  wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) wwit_unitSquareLoop := by
-- proof
  apply StatMech.Lattice.wos_unitSquare_signsAlternate

/--
[wos_Ltromino_signsAlternate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_Ltromino_signsAlternate_eq :
-- imply
  wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) wnu_LtrominoLoop := by
-- proof
  apply StatMech.Lattice.wos_Ltromino_signsAlternate

/--
[wos_unitSquare_columnAlternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_unitSquare_columnAlternates_eq :
-- imply
  wna_ColumnAlternates (![1, 1] : Site 2) wwit_unitSquareLoop := by
-- proof
  apply StatMech.Lattice.wos_unitSquare_columnAlternates

/--
[wos_Ltromino_columnAlternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_Ltromino_columnAlternates_eq :
-- imply
  wna_ColumnAlternates (![1, 1] : Site 2) wnu_LtrominoLoop := by
-- proof
  apply StatMech.Lattice.wos_Ltromino_columnAlternates

/--
[wos_twoToggle_alternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_twoToggle_alternates_eq :
-- imply
  wnu_Alt ([1, -1] : List ℤ) := by
-- proof
  apply StatMech.Lattice.wos_twoToggle_alternates

/--
[wos_twoToggle_neg_alternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_twoToggle_neg_alternates_eq :
-- imply
  wnu_Alt ([-1, 1] : List ℤ) := by
-- proof
  apply StatMech.Lattice.wos_twoToggle_neg_alternates

/--
[wos_twoToggle_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_twoToggle_eq_eq
  {M : List ℤ}
-- given
  (hM : wnu_Alt M)
  (hlen : M.length = 2)
  (hhead : M.headI = 1) :
-- imply
  M = [1, -1] := by
-- proof
  apply StatMech.Lattice.wos_twoToggle_eq M hM hlen hhead

/--
[wos_doubleSquare_list_not_alternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_doubleSquare_list_not_alternates_eq :
-- imply
  ¬ wnu_Alt ([1, 1] : List ℤ) := by
-- proof
  apply StatMech.Lattice.wos_doubleSquare_list_not_alternates

/--
[wos_doubleSquare_not_signsAlternate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wosorientedsign.lean)
-/
@[path]
private lemma wos_doubleSquare_not_signsAlternate_eq :
-- imply
  ¬ wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) wnu_doubleSquare := by
-- proof
  apply StatMech.Lattice.wos_doubleSquare_not_signsAlternate


-- created on 2026-10-23
