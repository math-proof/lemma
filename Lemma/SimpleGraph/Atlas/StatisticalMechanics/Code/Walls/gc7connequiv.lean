import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc7connequiv.Part2
open Finset BigOperators StatMech StatMech.Walls


/--
[gc7_connK_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean)
-/
@[path]
private lemma gc7_connK_refl_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {a : V} :
-- imply
  connK ends K a a := by
-- proof
  apply StatMech.Walls.gc7_connK_refl ends K a

/--
[gc7_connK_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean)
-/
@[path]
private lemma gc7_connK_symm_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {a b : V}
-- given
  (h : connK ends K a b) :
-- imply
  connK ends K b a := by
-- proof
  apply StatMech.Walls.gc7_connK_symm ends K h

/--
[gc7_connK_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean)
-/
@[path]
private lemma gc7_connK_trans_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {a b c : V}
-- given
  (h₁ : connK ends K a b)
  (h₂ : connK ends K b c) :
-- imply
  connK ends K a c := by
-- proof
  apply StatMech.Walls.gc7_connK_trans ends K h₁ h₂

/--
[gc7_connK_equivalence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean)
-/
@[path]
private lemma gc7_connK_equivalence_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι} :
-- imply
  Equivalence (connK ends K) := by
-- proof
  apply StatMech.Walls.gc7_connK_equivalence ends K

/--
[gc7_connSetoid_rel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean)
-/
@[path]
private lemma gc7_connSetoid_rel_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {a b : V} :
-- imply
  (gc7_connSetoid ends K) a b ↔ connK ends K a b := by
-- proof
  apply StatMech.Walls.gc7_connSetoid_rel ends K

/--
[gc7_connClasses_isPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean)
-/
@[path]
private lemma gc7_connClasses_isPartition_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι} :
-- imply
  Setoid.IsPartition (gc7_connSetoid ends K).classes := by
-- proof
  apply StatMech.Walls.gc7_connClasses_isPartition ends K

/--
[gc7_unique_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean)
-/
@[path]
private lemma gc7_unique_cluster_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {a : V} :
-- imply
  ∃! C, C ∈ (gc7_connSetoid ends K).classes ∧ a ∈ C := by
-- proof
  apply StatMech.Walls.gc7_unique_cluster ends K a

/--
[gc7_compOf_eq_class](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean)
-/
@[path]
private lemma gc7_compOf_eq_class_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {u : V} :
-- imply
  ((compOf ends K u : Finset V) : Set V) = {x | (gc7_connSetoid ends K) x u} := by
-- proof
  apply StatMech.Walls.gc7_compOf_eq_class ends K u

/--
[gc7_compOf_mem_classes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean)
-/
@[path]
private lemma gc7_compOf_mem_classes_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {u : V} :
-- imply
  ((compOf ends K u : Finset V) : Set V) ∈ (gc7_connSetoid ends K).classes := by
-- proof
  apply StatMech.Walls.gc7_compOf_mem_classes ends K u

/--
[gc7_odd_marks_unique_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean)
-/
@[path]
private lemma gc7_odd_marks_unique_cluster_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {o x y g : V} :
-- imply
  (∃! C, C ∈ (gc7_connSetoid ends K).classes ∧ o ∈ C) ∧ (∃! C, C ∈ (gc7_connSetoid ends K).classes ∧ x ∈ C) ∧ (∃! C, C ∈ (gc7_connSetoid ends K).classes ∧ y ∈ C) ∧ (∃! C, C ∈ (gc7_connSetoid ends K).classes ∧ g ∈ C) := by
-- proof
  apply StatMech.Walls.gc7_odd_marks_unique_cluster ends K o x y g

/--
[gc7_pair_in_one_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean)
-/
@[path]
private lemma gc7_pair_in_one_cluster_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {N : Finset (Copy G m)}
  {i j : V}
-- given
  (hbdry : sources (endsM G m) N = {i, j})
  (hij : i ≠ j) :
-- imply
  (gc7_connSetoid (endsM G m) (univ : Finset (Copy G m))) i j := by
-- proof
  apply StatMech.Walls.gc7_pair_in_one_cluster G m N hbdry hij

/--
[gc7_pair_same_class](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean)
-/
@[path]
private lemma gc7_pair_same_class_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {N : Finset (Copy G m)}
  {i j : V}
  {C : Set V}
-- given
  (hbdry : sources (endsM G m) N = {i, j})
  (hij : i ≠ j)
  (hC : C ∈ (gc7_connSetoid (endsM G m) (univ : Finset (Copy G m))).classes) :
-- imply
  i ∈ C ↔ j ∈ C := by
-- proof
  apply StatMech.Walls.gc7_pair_same_class G m N hbdry hij hC

/--
[gc7_two_pairs_share_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean)
-/
@[path]
private lemma gc7_two_pairs_share_cluster_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {i j k l : V}
-- given
  (hij : connK ends K i j)
  (hkl : connK ends K k l)
  (hik : connK ends K i k) :
-- imply
  connK ends K i j ∧ connK ends K i k ∧ connK ends K i l := by
-- proof
  apply StatMech.Walls.gc7_two_pairs_share_cluster ends K hij hkl hik

/--
[gc7_four_marks_one_class](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean)
-/
@[path]
private lemma gc7_four_marks_one_class_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {K : Finset ι}
  {i j k l : V}
-- given
  (hij : connK ends K i j)
  (hkl : connK ends K k l)
  (hik : connK ends K i k) :
-- imply
  let C := {x : V | (gc7_connSetoid ends K) x i} i ∈ C ∧ j ∈ C ∧ k ∈ C ∧ l ∈ C := by
-- proof
  apply StatMech.Walls.gc7_four_marks_one_class ends K hij hkl hik

/--
[gc7_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean)
-/
@[path]
private lemma gc7_nonvacuous_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  Setoid.IsPartition (gc7_connSetoid (fun _ : Fin 1 => (s(0, 1) : Sym2 (Fin 2))) (univ : Finset (Fin 1))).classes := by
-- proof
  apply StatMech.Walls.gc7_nonvacuous

/--
[gc7_unique_cluster_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc7connequiv.lean)
-/
@[path]
private lemma gc7_unique_cluster_nonvacuous_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {a : Fin 2} :
-- imply
  ∃! C, C ∈ (gc7_connSetoid (fun _ : Fin 1 => (s(0, 1) : Sym2 (Fin 2))) (univ : Finset (Fin 1))).classes ∧ a ∈ C := by
-- proof
  apply StatMech.Walls.gc7_unique_cluster_nonvacuous a


-- created on 2026-10-23
