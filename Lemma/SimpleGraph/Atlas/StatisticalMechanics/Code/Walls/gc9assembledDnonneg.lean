import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc9assembledDnonneg.Part4
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc9_assembled_D_term_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9assembledDnonneg.lean)
-/
@[path]
private lemma gc9_assembled_D_term_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {J : Sym2 V → ℝ}
  {δ : V → V → ℝ}
  {x y : V}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hδ : ∀ x y, 0 ≤ δ x y) :
-- imply
  0 ≤ J s(x, y) * δ x y := by
-- proof
  apply StatMech.Walls.gc9_assembled_D_term_nonneg J δ hJ hδ x y

/--
[gc9_assembled_D_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9assembledDnonneg.lean)
-/
@[path]
private lemma gc9_assembled_D_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {J : Sym2 V → ℝ}
  {δ : V → V → ℝ}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hδ : ∀ x y, 0 ≤ δ x y) :
-- imply
  0 ≤ ∑ x : V, ∑ y : V, J s(x, y) * δ x y := by
-- proof
  apply StatMech.Walls.gc9_assembled_D_nonneg J δ hJ hδ

/--
[gc9_assembled_D_edges_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9assembledDnonneg.lean)
-/
@[path]
private lemma gc9_assembled_D_edges_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {J : Sym2 V → ℝ}
  {δe : Sym2 V → ℝ}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hδ : ∀ e, 0 ≤ δe e) :
-- imply
  0 ≤ ∑ e : Sym2 V, J e * δe e := by
-- proof
  apply StatMech.Walls.gc9_assembled_D_edges_nonneg J δe hJ hδ

/--
[gc9_concrete_delta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9assembledDnonneg.lean)
-/
@[path]
private lemma gc9_concrete_delta_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o g x y : V}
-- given
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  0 ≤ gc9_pivotalMass ends F o g x y := by
-- proof
  apply StatMech.Walls.gc9_concrete_delta_nonneg ends F hF o g x y

/--
[gc9_assembledD_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9assembledDnonneg.lean)
-/
@[path]
private lemma gc9_assembledD_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {J : Sym2 V → ℝ}
  {o g : V}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  0 ≤ gc9_assembledD ends F J o g := by
-- proof
  apply StatMech.Walls.gc9_assembledD_nonneg ends F J o g hJ hF

/--
[gc9_assembledD_disconn_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9assembledDnonneg.lean)
-/
@[path]
private lemma gc9_assembledD_disconn_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {J : Sym2 V → ℝ}
  {o g : V}
-- given
  (hJ : ∀ e, 0 ≤ J e)
  (hF : ∀ m, 0 ≤ F m)
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hdist : ∀ x y : V, o ≠ x ∧ o ≠ y ∧ o ≠ g ∧ x ≠ y ∧ x ≠ g ∧ y ≠ g)
  (hsrcSet : ∀ x y : V, ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
-- imply
  0 ≤ gc9_assembledD_disconn ends F J o g := by
-- proof
  apply StatMech.Walls.gc9_assembledD_disconn_nonneg ends F J o g hJ hF hnd hdist hsrcSet

/--
[gc9_assembled_D_nonneg_independent_of_u3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9assembledDnonneg.lean)
-/
@[path]
private lemma gc9_assembled_D_nonneg_independent_of_u3_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {J : Sym2 V → ℝ}
  {δ : V → V → ℝ} :
-- imply
  (∀ e, 0 ≤ J e) → (∀ x y, 0 ≤ δ x y) → 0 ≤ ∑ x : V, ∑ y : V, J s(x, y) * δ x y := by
-- proof
  apply StatMech.Walls.gc9_assembled_D_nonneg_independent_of_u3 J δ

/--
[gc9_assembled_D_nonneg_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9assembledDnonneg.lean)
-/
@[path]
private lemma gc9_assembled_D_nonneg_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι] :
-- imply
  0 ≤ gc9_assembledD (witEnds : Fin 2 → Sym2 (Fin 4)) (fun _ => 1) (fun _ => 1) (0 : Fin 4) 3 := by
-- proof
  apply StatMech.Walls.gc9_assembled_D_nonneg_nonvacuous


-- created on 2026-10-23
