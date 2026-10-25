import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc8crossingallconn
open Finset BigOperators Classical StatMech StatMech.Walls


/--
[gc8_caseB_eq_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8crossingallconn.lean)
-/
@[path]
private lemma gc8_caseB_eq_swap_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {o x y g : V}
  {m : Finset ι} :
-- imply
  gc8_caseB ends o x y g m = gc8_caseA ends o y x g m := by
-- proof
  apply StatMech.Walls.gc8_caseB_eq_swap ends o x y g m

/--
[gc8_four_marks_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8crossingallconn.lean)
-/
@[path]
private lemma gc8_four_marks_even_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  Even (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card := by
-- proof
  apply StatMech.Walls.gc8_four_marks_even o x y hox hoy hxy

/--
[gc8_caseA_caseB_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8crossingallconn.lean)
-/
@[path]
private lemma gc8_caseA_caseB_disjoint_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources ends m = {o, x, y, g}) :
-- imply
  ¬ (gc8_caseA ends o x y g m ∧ gc8_caseB ends o x y g m) := by
-- proof
  apply StatMech.Walls.gc8_caseA_caseB_disjoint ends m hnd o x y g hox hoy hog hxy hxg hyg hsrc

/--
[gc8_disconn_eq_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8crossingallconn.lean)
-/
@[path]
private lemma gc8_disconn_eq_union_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources ends m = {o, x, y, g}) :
-- imply
  gc8_disconn ends o g m ↔ (gc8_caseA ends o x y g m ∨ gc8_caseB ends o x y g m) := by
-- proof
  apply StatMech.Walls.gc8_disconn_eq_union ends m hnd o x y g hox hoy hog hxy hxg hyg hsrc

/--
[gc8_disconn_indicator_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8crossingallconn.lean)
-/
@[path]
private lemma gc8_disconn_indicator_split_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources ends m = {o, x, y, g}) :
-- imply
  (if gc8_disconn ends o g m then (1 : ℝ) else 0) = (if gc8_disconn ends o g m ∧ (connK ends m o x ∧ connK ends m y g) then 1 else 0) + (if gc8_disconn ends o g m ∧ (connK ends m o y ∧ connK ends m x g) then 1 else 0) := by
-- proof
  apply StatMech.Walls.gc8_disconn_indicator_split ends m hnd o x y g hox hoy hog hxy hxg hyg hsrc

/--
[gc8_delta_eq_caseA_plus_caseB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8crossingallconn.lean)
-/
@[path]
private lemma gc8_delta_eq_caseA_plus_caseB_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o x y g : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
-- imply
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m) = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m) + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) := by
-- proof
  apply StatMech.Walls.gc8_delta_eq_caseA_plus_caseB ends F hox hoy hog hxy hxg hyg hnd hsrcSet

/--
[gc8_caseB_pairSum_eq_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8crossingallconn.lean)
-/
@[path]
private lemma gc8_caseB_pairSum_eq_swap_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o x y g : V} :
-- imply
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) = drd_pairSum ends ({o, y, x, g} : Finset V) F (fun m => gc8_caseA ends o y x g m) := by
-- proof
  apply StatMech.Walls.gc8_caseB_pairSum_eq_swap ends F o x y g

/--
[gc8_crossingAllConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8crossingallconn.lean)
-/
@[path]
private lemma gc8_crossingAllConn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o x y g : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
-- imply
  (∀ m : Finset ι, gc8_caseB ends o x y g m = gc8_caseA ends o y x g m) ∧ (∀ m : Finset ι, (∀ i ∈ m, ¬ (ends i).IsDiag) → sources ends m = {o, x, y, g} → ¬ (gc8_caseA ends o x y g m ∧ gc8_caseB ends o x y g m)) ∧ (∀ m : Finset ι, (∀ i ∈ m, ¬ (ends i).IsDiag) → sources ends m = {o, x, y, g} → (gc8_disconn ends o g m ↔ (gc8_caseA ends o x y g m ∨ gc8_caseB ends o x y g m))) ∧ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m) = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m) + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) := by
-- proof
  apply StatMech.Walls.gc8_crossingAllConn ends F hox hoy hog hxy hxg hyg hnd hsrcSet

/--
[gc8_pathCrossing_input](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8crossingallconn.lean)
-/
@[path]
private lemma gc8_pathCrossing_input_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y g : V}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources ends m = {o, x, y, g})
  (hdisc : ¬ connK ends m o g) :
-- imply
  ((connK ends m o x ∧ connK ends m y g) ∨ (connK ends m o y ∧ connK ends m x g)) ∧ ¬ ((connK ends m o x ∧ connK ends m y g) ∧ (connK ends m o y ∧ connK ends m x g)) := by
-- proof
  apply StatMech.Walls.gc8_pathCrossing_input ends m hnd o x y g hox hoy hog hxy hxg hyg hsrc hdisc

/--
[gc8_crossingAllConn_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8crossingallconn.lean)
-/
@[path]
private lemma gc8_crossingAllConn_nonvacuous_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V] :
-- imply
  let ends : Fin 2 → Sym2 (Fin 4) := witEnds sources ends witM = ({0, 1, 2, 3} : Finset (Fin 4)) ∧ gc8_caseA ends (0 : Fin 4) 1 2 3 witM ∧ ¬ gc8_caseB ends (0 : Fin 4) 1 2 3 witM := by
-- proof
  apply StatMech.Walls.gc8_crossingAllConn_nonvacuous


-- created on 2026-10-23
