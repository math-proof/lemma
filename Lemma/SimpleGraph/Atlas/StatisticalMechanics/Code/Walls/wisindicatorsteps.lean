import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.wisindicatorsteps
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[wis_ind_in_01](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_ind_in_01_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c : ℤ} :
-- imply
  wis_ind z Vc c = 0 ∨ wis_ind z Vc c = 1 := by
-- proof
  apply StatMech.Lattice.wis_ind_in_01 z Vc c

/--
[wis_rowCell_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_rowCell_step_eq
  {z : Site 2}
  {c : ℤ} :
-- imply
  (![c + 1, z 1] : Site 2) 0 = (![c, z 1] : Site 2) 0 + 1 ∧ (![c + 1, z 1] : Site 2) 1 = (![c, z 1] : Site 2) 1 := by
-- proof
  apply StatMech.Lattice.wis_rowCell_step z c

/--
[wis_ind_step_neq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_ind_step_neq_iff_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c : ℤ} :
-- imply
  wis_ind z Vc (c + 1) ≠ wis_ind z Vc c ↔ Odd (Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2))) := by
-- proof
  apply StatMech.Lattice.wis_ind_step_neq_iff z Vc c

/--
[wis_take_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_take_filter_eq
  {p : α → Bool}
  {L : List α}
  {k : ℕ} :
-- imply
  ∃ j ≤ L.length, (L.filter p).take k = (L.take j).filter p := by
-- proof
  apply StatMech.Lattice.wis_take_filter p L k

/--
[wis_take_nonzeroDiffs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_take_nonzeroDiffs_eq
  {f : ℕ → ℤ}
  {n k : ℕ} :
-- imply
  ∃ m ≤ n, (wis_nonzeroDiffs f n).take k = wis_nonzeroDiffs f m := by
-- proof
  apply StatMech.Lattice.wis_take_nonzeroDiffs f n k

/--
[wis_nonzeroDiffs_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_nonzeroDiffs_sum_eq
  {f : ℕ → ℤ}
  {n : ℕ}
-- given
  (h0 : f 0 = 0) :
-- imply
  (wis_nonzeroDiffs f n).sum = f n := by
-- proof
  apply StatMech.Lattice.wis_nonzeroDiffs_sum f h0 n

/--
[wis_nonzeroDiffs_isIndicatorStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_nonzeroDiffs_isIndicatorStep_eq
  {f : ℕ → ℤ}
  {n : ℕ}
-- given
  (h01 : ∀ n, f n = 0 ∨ f n = 1)
  (h0 : f 0 = 0) :
-- imply
  ∃ ind : ℕ → ℤ, (∀ e ∈ wis_nonzeroDiffs f n, e = 1 ∨ e = -1) ∧ ind 0 = 0 ∧ (∀ m, ind m = 0 ∨ ind m = 1) ∧ wis_nonzeroDiffs f n = (List.range (wis_nonzeroDiffs f n).length).map (fun i => ind (i + 1) - ind i) := by
-- proof
  apply StatMech.Lattice.wis_nonzeroDiffs_isIndicatorStep f h01 h0 n

/--
[wis_indSeq_in_01](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_indSeq_in_01_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c₀ : ℤ}
  {i : ℕ} :
-- imply
  wis_indSeq z Vc c₀ i = 0 ∨ wis_indSeq z Vc c₀ i = 1 := by
-- proof
  apply StatMech.Lattice.wis_indSeq_in_01 z Vc c₀ i

/--
[wis_nonzeroDiffs_neg_isIndicatorStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_nonzeroDiffs_neg_isIndicatorStep_eq
  {f : ℕ → ℤ}
  {n : ℕ}
-- given
  (h01 : ∀ n, f n = 0 ∨ f n = 1)
  (h0 : f 0 = 0) :
-- imply
  ∃ ind : ℕ → ℤ, (∀ e ∈ wis_nonzeroDiffs (fun i => - f i) n, e = 1 ∨ e = -1) ∧ ind 0 = 0 ∧ (∀ m, ind m = 0 ∨ ind m = -1) ∧ wis_nonzeroDiffs (fun i => - f i) n = (List.range (wis_nonzeroDiffs (fun i => - f i) n).length).map (fun i => ind (i + 1) - ind i) := by
-- proof
  apply StatMech.Lattice.wis_nonzeroDiffs_neg_isIndicatorStep f h01 h0 n

/--
[wis_indicatorSteps_of_signEqJumps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_indicatorSteps_of_signEqJumps_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wis_SignEqIndicatorJumps z Vc) :
-- imply
  wst_IndicatorSteps z Vc := by
-- proof
  apply StatMech.Lattice.wis_indicatorSteps_of_signEqJumps z Vc h

/--
[wis_columnAlternates_of_signEqJumps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_columnAlternates_of_signEqJumps_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wis_SignEqIndicatorJumps z Vc) :
-- imply
  wna_ColumnAlternates z Vc := by
-- proof
  apply StatMech.Lattice.wis_columnAlternates_of_signEqJumps z Vc h

/--
[wis_unitSquare_rayCount0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_unitSquare_rayCount0_eq :
-- imply
  jec_rayCount (![0, 1] : Site 2) wwit_unitSquareLoop = 0 := by
-- proof
  apply StatMech.Lattice.wis_unitSquare_rayCount0

/--
[wis_unitSquare_rayCount1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_unitSquare_rayCount1_eq :
-- imply
  jec_rayCount (![1, 1] : Site 2) wwit_unitSquareLoop = 1 := by
-- proof
  apply StatMech.Lattice.wis_unitSquare_rayCount1

/--
[wis_unitSquare_signEqJumps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_unitSquare_signEqJumps_eq :
-- imply
  wis_SignEqIndicatorJumps (![1, 1] : Site 2) wwit_unitSquareLoop := by
-- proof
  apply StatMech.Lattice.wis_unitSquare_signEqJumps

/--
[wis_Ltromino_rayCount0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_Ltromino_rayCount0_eq :
-- imply
  jec_rayCount (![0, 1] : Site 2) wnu_LtrominoLoop = 0 := by
-- proof
  apply StatMech.Lattice.wis_Ltromino_rayCount0

/--
[wis_Ltromino_rayCount1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_Ltromino_rayCount1_eq :
-- imply
  jec_rayCount (![1, 1] : Site 2) wnu_LtrominoLoop = 1 := by
-- proof
  apply StatMech.Lattice.wis_Ltromino_rayCount1

/--
[wis_Ltromino_signEqJumps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_Ltromino_signEqJumps_eq :
-- imply
  wis_SignEqIndicatorJumps (![1, 1] : Site 2) wnu_LtrominoLoop := by
-- proof
  apply StatMech.Lattice.wis_Ltromino_signEqJumps

/--
[wis_doubleSquare_not_signEqJumps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_doubleSquare_not_signEqJumps_eq :
-- imply
  ¬ wis_SignEqIndicatorJumps (![1, 1] : Site 2) wnu_doubleSquare := by
-- proof
  apply StatMech.Lattice.wis_doubleSquare_not_signEqJumps

/--
[wis_twoToggle_nonzeroDiffs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_twoToggle_nonzeroDiffs_eq :
-- imply
  wis_nonzeroDiffs wis_twoToggle 3 = [1, -1] := by
-- proof
  apply StatMech.Lattice.wis_twoToggle_nonzeroDiffs

/--
[wis_twoToggle_isIndicatorStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_twoToggle_isIndicatorStep_eq :
-- imply
  ∃ ind : ℕ → ℤ, (∀ e ∈ ([1, -1] : List ℤ), e = 1 ∨ e = -1) ∧ ind 0 = 0 ∧ (∀ m, ind m = 0 ∨ ind m = 1) ∧ ([1, -1] : List ℤ) = (List.range 2).map (fun i => ind (i + 1) - ind i) := by
-- proof
  apply StatMech.Lattice.wis_twoToggle_isIndicatorStep

/--
[wis_twoToggle_alternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean)
-/
@[path]
private lemma wis_twoToggle_alternates_eq :
-- imply
  wnu_Alt ([1, -1] : List ℤ) := by
-- proof
  apply StatMech.Lattice.wis_twoToggle_alternates


-- created on 2026-10-23
