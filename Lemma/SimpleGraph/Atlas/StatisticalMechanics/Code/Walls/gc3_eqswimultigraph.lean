import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc3_eqswimultigraph
open Finset BigOperators Classical StatMech StatMech.Walls


/--
[gc3_count_collapse_of_FB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_eqswimultigraph.lean)
-/
@[path]
private lemma gc3_count_collapse_of_FB_eq
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
  apply StatMech.Walls.gc3_count_collapse_of_FB ends M hFB

/--
[gc3_count_zero_of_not_FB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_eqswimultigraph.lean)
-/
@[path]
private lemma gc3_count_zero_of_not_FB_eq
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
  apply StatMech.Walls.gc3_count_zero_of_not_FB ends M hnd hFB

/--
[gc3_eqSwi_multigraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_eqswimultigraph.lean)
-/
@[path]
private lemma gc3_eqSwi_multigraph_eq
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
  apply StatMech.Walls.gc3_eqSwi_multigraph ends M hnd B

/--
[gc3_eqSwi_multigraph_current](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_eqswimultigraph.lean)
-/
@[path]
private lemma gc3_eqSwi_multigraph_current_eq
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
  apply StatMech.Walls.gc3_eqSwi_multigraph_current G m M B

/--
[gc3_eqSwi_multigraph_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_eqswimultigraph.lean)
-/
@[path]
private lemma gc3_eqSwi_multigraph_univ_eq
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
  apply StatMech.Walls.gc3_eqSwi_multigraph_univ G m B

/--
[gc3_eqSwi_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_eqswimultigraph.lean)
-/
@[path]
private lemma gc3_eqSwi_split_eq
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
  (∑ n : {p : ↥G.edgeFinset → ℕ // p ≤ m}, (if StatMech.Sharpness.sources G (ofEdgeFun G n.1) = B then (∏ e : ↥G.edgeFinset, (m e).choose (n.1 e)) else 0)) = (if gc2_FB (endsM G m) (Finset.univ : Finset (Copy G m)) B then 1 else 0) * (∑ n : {p : ↥G.edgeFinset → ℕ // p ≤ m}, (if StatMech.Sharpness.sources G (ofEdgeFun G n.1) = ∅ then (∏ e : ↥G.edgeFinset, (m e).choose (n.1 e)) else 0)) := by
-- proof
  apply StatMech.Walls.gc3_eqSwi_split G m B

/--
[gc3_threeReplica_binomFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_eqswimultigraph.lean)
-/
@[path]
private lemma gc3_threeReplica_binomFactor_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {m n₁ : ↥G.edgeFinset → ℕ} :
-- imply
  (∏ e : ↥G.edgeFinset, ((ofEdgeFun G m) e.1).choose ((ofEdgeFun G n₁) e.1)) = ∏ e : ↥G.edgeFinset, (m e).choose (n₁ e) := by
-- proof
  apply StatMech.Walls.gc3_threeReplica_binomFactor G m n₁

/--
[gc3_eqSwi_split_threeReplica](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc3_eqswimultigraph.lean)
-/
@[path]
private lemma gc3_eqSwi_split_threeReplica_eq
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
  apply StatMech.Walls.gc3_eqSwi_split_threeReplica G m A


-- created on 2026-10-23
