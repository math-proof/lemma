import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc10switching
open Finset BigOperators Classical StatMech StatMech.Walls


/--
[gc10_switching_difference_to_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10switching.lean)
-/
@[path]
private lemma gc10_switching_difference_to_delta_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {A : Finset V}
  {o g : V}
-- given
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hog : o ≠ g) :
-- imply
  drd_pairSum ends A F (fun m => gc8_disconn ends o g m) = (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A), F m)) - (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A ∆ {o, g}), F m)) := by
-- proof
  apply StatMech.Walls.gc10_switching_difference_to_delta ends F A hnd hog

/--
[gc10_switching_difference_to_disconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10switching.lean)
-/
@[path]
private lemma gc10_switching_difference_to_disconn_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {A : Finset V}
  {o g : V}
-- given
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hog : o ≠ g) :
-- imply
  drd_pairSum ends A F (fun m => ¬ connK ends m o g) = (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A), F m)) - (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A ∆ {o, g}), F m)) := by
-- proof
  apply StatMech.Walls.gc10_switching_difference_to_disconn ends F A hnd hog

/--
[gc10_switching_difference_to_gate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10switching.lean)
-/
@[path]
private lemma gc10_switching_difference_to_gate_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {A : Finset V}
  {o g : V}
  {F : Finset ι → ℝ}
-- given
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hog : o ≠ g) :
-- imply
  (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A), F m)) - (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A ∆ {o, g}), F m)) = ∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A), F m * (if ¬ connK ends m o g then 1 else 0)) := by
-- proof
  apply StatMech.Walls.gc10_switching_difference_to_gate ends hnd A hog F

/--
[gc10_eqswi_vanishing_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10switching.lean)
-/
@[path]
private lemma gc10_eqswi_vanishing_branch_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset ι}
  {B : Finset V}
-- given
  (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag)
  (hFB : ¬ gc2_FB ends M B) :
-- imply
  #(M.powerset.filter (fun N => RandomCurrent.sources ends N = B)) = 0 := by
-- proof
  apply StatMech.Walls.gc10_eqswi_vanishing_branch ends M hnd hFB

/--
[gc10_eqswi_count_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10switching.lean)
-/
@[path]
private lemma gc10_eqswi_count_collapse_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset ι}
  {B : Finset V}
-- given
  (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) :
-- imply
  #(M.powerset.filter (fun N => RandomCurrent.sources ends N = B)) = (if gc2_FB ends M B then 1 else 0) * #(M.powerset.filter (fun N => RandomCurrent.sources ends N = ∅)) := by
-- proof
  apply StatMech.Walls.gc10_eqswi_count_collapse ends M hnd B

/--
[gc10_switching_eqswi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10switching.lean)
-/
@[path]
private lemma gc10_switching_eqswi_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {A : Finset V}
  {o g : V}
  {B : Finset V}
-- given
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hog : o ≠ g) :
-- imply
  (drd_pairSum ends A F (fun m => gc8_disconn ends o g m) = (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A), F m)) - (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A ∆ {o, g}), F m))) ∧ #(Finset.univ.powerset.filter (fun N => RandomCurrent.sources ends N = B)) = (if gc2_FB ends Finset.univ B then 1 else 0) * #(Finset.univ.powerset.filter (fun N => RandomCurrent.sources ends N = ∅)) := by
-- proof
  apply StatMech.Walls.gc10_switching_eqswi ends F A hnd hog B

/--
[gc10_delta_eq_switching_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10switching.lean)
-/
@[path]
private lemma gc10_delta_eq_switching_gap_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {A : Finset V}
  {o g : V}
-- given
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hog : o ≠ g) :
-- imply
  drd_pairSum ends A F (fun m => gc8_disconn ends o g m) = (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A), F m)) - (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A ∆ {o, g}), F m)) := by
-- proof
  apply StatMech.Walls.gc10_delta_eq_switching_gap ends F A hnd hog

/--
[gc10_switching_difference_to_delta_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10switching.lean)
-/
@[path]
private lemma gc10_switching_difference_to_delta_nonvacuous_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  drd_pairSum witEnds ({0, 1, 2, 3} : Finset (Fin 4)) (fun _ => 1) (fun m => gc8_disconn witEnds (0 : Fin 4) 3 m) = (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources witEnds m = ({0, 1, 2, 3} : Finset (Fin 4)))), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources witEnds K = ({0, 1, 2, 3} : Finset (Fin 4))), (fun _ => (1 : ℝ)) m)) - (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources witEnds m = ({0, 1, 2, 3} : Finset (Fin 4)))), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources witEnds K = ({0, 1, 2, 3} : Finset (Fin 4)) ∆ {(0 : Fin 4), 3}), (fun _ => (1 : ℝ)) m)) := by
-- proof
  apply StatMech.Walls.gc10_switching_difference_to_delta_nonvacuous


-- created on 2026-10-23
