import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc5_eqswi
open Finset BigOperators Classical StatMech StatMech.Walls


/--
[gc5_eqSwi_engine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_eqswi.lean)
-/
@[path]
private lemma gc5_eqSwi_engine_eq
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
  #(M.powerset.filter (fun N => sources ends N = B)) = (if gc2_FB ends M B then 1 else 0) * #(M.powerset.filter (fun N => sources ends N = ∅)) := by
-- proof
  apply StatMech.Walls.gc5_eqSwi_engine ends M hnd B

/--
[gc5_eqSwi_vanishing_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_eqswi.lean)
-/
@[path]
private lemma gc5_eqSwi_vanishing_branch_eq
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
  #(M.powerset.filter (fun N => sources ends N = B)) = 0 := by
-- proof
  apply StatMech.Walls.gc5_eqSwi_vanishing_branch ends M hnd hFB

/--
[gc5_eqSwi_positive_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_eqswi.lean)
-/
@[path]
private lemma gc5_eqSwi_positive_branch_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset ι}
  {B : Finset V}
-- given
  (hFB : gc2_FB ends M B) :
-- imply
  #(M.powerset.filter (fun N => sources ends N = B)) = #(M.powerset.filter (fun N => sources ends N = ∅)) := by
-- proof
  apply StatMech.Walls.gc5_eqSwi_positive_branch ends M hFB

/--
[gc5_eqSwi_engine_iff_FB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_eqswi.lean)
-/
@[path]
private lemma gc5_eqSwi_engine_iff_FB_eq
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
  (gc2_FB ends M B → #(M.powerset.filter (fun N => sources ends N = B)) = #(M.powerset.filter (fun N => sources ends N = ∅))) ∧ (¬ gc2_FB ends M B → #(M.powerset.filter (fun N => sources ends N = B)) = 0) := by
-- proof
  apply StatMech.Walls.gc5_eqSwi_engine_iff_FB ends M hnd B

/--
[gc5_eqSwi_threeReplica](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_eqswi.lean)
-/
@[path]
private lemma gc5_eqSwi_threeReplica_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {M : Finset (Copy G m)}
  {B : Finset W} :
-- imply
  #(M.powerset.filter (fun N => RandomCurrent.sources (endsM G m) N = B)) = (if gc2_FB (endsM G m) M B then 1 else 0) * #(M.powerset.filter (fun N => RandomCurrent.sources (endsM G m) N = ∅)) := by
-- proof
  apply StatMech.Walls.gc5_eqSwi_threeReplica G m M B

/--
[gc5_eqSwi_threeReplica_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_eqswi.lean)
-/
@[path]
private lemma gc5_eqSwi_threeReplica_univ_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {B : Finset W} :
-- imply
  #((Finset.univ : Finset (Copy G m)).powerset.filter (fun N => RandomCurrent.sources (endsM G m) N = B)) = (if gc2_FB (endsM G m) (Finset.univ : Finset (Copy G m)) B then 1 else 0) * #((Finset.univ : Finset (Copy G m)).powerset.filter (fun N => RandomCurrent.sources (endsM G m) N = ∅)) := by
-- proof
  apply StatMech.Walls.gc5_eqSwi_threeReplica_univ G m B

/--
[gc5_eqSwi_split_threeReplica](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_eqswi.lean)
-/
@[path]
private lemma gc5_eqSwi_split_threeReplica_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {A : Finset W} :
-- imply
  (∑ n₁ : {p : ↥G.edgeFinset → ℕ // p ≤ m}, (if StatMech.Sharpness.sources G (ofEdgeFun G n₁.1) = A then (∏ e : ↥G.edgeFinset, ((ofEdgeFun G m) e.1).choose ((ofEdgeFun G n₁.1) e.1)) else 0)) = (if gc2_FB (endsM G m) (Finset.univ : Finset (Copy G m)) A then 1 else 0) * (∑ n₁ : {p : ↥G.edgeFinset → ℕ // p ≤ m}, (if StatMech.Sharpness.sources G (ofEdgeFun G n₁.1) = ∅ then (∏ e : ↥G.edgeFinset, ((ofEdgeFun G m) e.1).choose ((ofEdgeFun G n₁.1) e.1)) else 0)) := by
-- proof
  apply StatMech.Walls.gc5_eqSwi_split_threeReplica G m A


-- created on 2026-10-23
