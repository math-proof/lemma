import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc9deltadef
open Finset BigOperators Classical StatMech StatMech.Walls


/--
[gc9_delta_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9deltadef.lean)
-/
@[path]
private lemma gc9_delta_def_eq
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
  gc9_delta ends F o x y g = gc9_delta_caseA ends F o x y g + gc9_delta_caseB ends F o x y g := by
-- proof
  apply StatMech.Walls.gc9_delta_def ends F hox hoy hog hxy hxg hyg hnd hsrcSet

/--
[gc9_delta_caseA_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9deltadef.lean)
-/
@[path]
private lemma gc9_delta_caseA_eq_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o x y g : V} :
-- imply
  gc9_delta_caseA ends F o x y g = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => (¬ connK ends m o g) ∧ (connK ends m o x ∧ connK ends m y g)) := by
-- proof
  apply StatMech.Walls.gc9_delta_caseA_eq ends F o x y g

/--
[gc9_delta_caseB_eq_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9deltadef.lean)
-/
@[path]
private lemma gc9_delta_caseB_eq_swap_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o x y g : V} :
-- imply
  gc9_delta_caseB ends F o x y g = gc9_delta_caseA ends F o y x g := by
-- proof
  apply StatMech.Walls.gc9_delta_caseB_eq_swap ends F o x y g

/--
[gc9_delta_caseA_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9deltadef.lean)
-/
@[path]
private lemma gc9_delta_caseA_nonneg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o x y g : V}
-- given
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  0 ≤ gc9_delta_caseA ends F o x y g := by
-- proof
  apply StatMech.Walls.gc9_delta_caseA_nonneg ends F o x y g hF

/--
[gc9_delta_caseB_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9deltadef.lean)
-/
@[path]
private lemma gc9_delta_caseB_nonneg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o x y g : V}
-- given
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  0 ≤ gc9_delta_caseB ends F o x y g := by
-- proof
  apply StatMech.Walls.gc9_delta_caseB_nonneg ends F o x y g hF

/--
[gc9_delta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9deltadef.lean)
-/
@[path]
private lemma gc9_delta_nonneg_eq
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
  (hF : ∀ m, 0 ≤ F m)
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
-- imply
  0 ≤ gc9_delta ends F o x y g := by
-- proof
  apply StatMech.Walls.gc9_delta_nonneg ends F hox hoy hog hxy hxg hyg hnd hF hsrcSet

/--
[gc9_deltaDef](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9deltadef.lean)
-/
@[path]
private lemma gc9_deltaDef_eq
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
  (hF : ∀ m, 0 ≤ F m)
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
-- imply
  (gc9_delta ends F o x y g = gc9_delta_caseA ends F o x y g + gc9_delta_caseB ends F o x y g) ∧ (gc9_delta_caseB ends F o x y g = gc9_delta_caseA ends F o y x g) ∧ (0 ≤ gc9_delta ends F o x y g) := by
-- proof
  apply StatMech.Walls.gc9_deltaDef ends F hox hoy hog hxy hxg hyg hnd hF hsrcSet

/--
[gc9_delta_def_consistent_pivotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9deltadef.lean)
-/
@[path]
private lemma gc9_delta_def_consistent_pivotal_eq
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
  apply StatMech.Walls.gc9_delta_def_consistent_pivotal ends F hox hoy hog hxy hxg hyg hnd hsrcSet

/--
[gc9_delta_nonneg_consistent_pivotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9deltadef.lean)
-/
@[path]
private lemma gc9_delta_nonneg_consistent_pivotal_eq
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
  (hF : ∀ m, 0 ≤ F m)
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
-- imply
  0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m) := by
-- proof
  apply StatMech.Walls.gc9_delta_nonneg_consistent_pivotal ends F hox hoy hog hxy hxg hyg hnd hF hsrcSet

/--
[gc9_delta_def_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9deltadef.lean)
-/
@[path]
private lemma gc9_delta_def_nonvacuous_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V] :
-- imply
  let ends : Fin 2 → Sym2 (Fin 4) := witEnds sources ends witM = ({0, 1, 2, 3} : Finset (Fin 4)) ∧ gc8_caseA ends (0 : Fin 4) 1 2 3 witM ∧ ¬ gc8_caseB ends (0 : Fin 4) 1 2 3 witM := by
-- proof
  apply StatMech.Walls.gc9_delta_def_nonvacuous


-- created on 2026-10-23
