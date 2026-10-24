import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gc2_core
open Finset BigOperators Classical StatMech StatMech.Walls


/--
[gc2_compOf_eq_of_connK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_core.lean)
-/
@[path]
private lemma gc2_compOf_eq_of_connK_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset ι}
  {u v : V}
-- given
  (h : connK ends M u v) :
-- imply
  compOf ends M u = compOf ends M v := by
-- proof
  apply StatMech.Walls.gc2_compOf_eq_of_connK ends M h

/--
[gc2_FB_pair_within_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_core.lean)
-/
@[path]
private lemma gc2_FB_pair_within_cluster_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset ι}
  {B : Finset V}
  {u : V}
-- given
  (hFB : gc2_FB ends M B)
  (hu : u ∈ B) :
-- imply
  ∃ v ∈ B, v ≠ u ∧ connK ends M u v := by
-- proof
  apply StatMech.Walls.gc2_FB_pair_within_cluster ends M B hFB hu

/--
[gc2_FB_remove_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_core.lean)
-/
@[path]
private lemma gc2_FB_remove_pair_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset ι}
  {B : Finset V}
  {u v : V}
-- given
  (huv : u ≠ v)
  (hu : u ∈ B)
  (hv : v ∈ B)
  (hconn : connK ends M u v)
  (hFB : gc2_FB ends M B) :
-- imply
  gc2_FB ends M (B ∆ {u, v}) := by
-- proof
  apply StatMech.Walls.gc2_FB_remove_pair ends M B huv hu hv hconn hFB

/--
[gc2_minlenDisjoint_K_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_core.lean)
-/
@[path]
private lemma gc2_minlenDisjoint_K_exists_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset ι} :
-- imply
  ∀ (B : Finset V), gc2_FB ends M B → ∃ K ⊆ M, sources ends K = B := by
-- proof
  apply StatMech.Walls.gc2_minlenDisjoint_K_exists ends M

/--
[gc2_splice_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_core.lean)
-/
@[path]
private lemma gc2_splice_boundary_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {P P' : Finset ι} :
-- imply
  sources ends (P ∆ P') = sources ends P ∆ sources ends P' := by
-- proof
  apply StatMech.Walls.gc2_splice_boundary ends P P'

/--
[gc2_splice_shorter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_core.lean)
-/
@[path]
private lemma gc2_splice_shorter_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {P P' : Finset ι}
  {i : ι}
-- given
  (hiP : i ∈ P)
  (hiP' : i ∈ P') :
-- imply
  #(P ∆ P') < #P + #P' := by
-- proof
  apply StatMech.Walls.gc2_splice_shorter P P' hiP hiP'

/--
[gc2_splice_surgery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_core.lean)
-/
@[path]
private lemma gc2_splice_surgery_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M P P' : Finset ι}
  {i : ι}
-- given
  (hPM : P ⊆ M)
  (hP'M : P' ⊆ M)
  (hiP : i ∈ P)
  (hiP' : i ∈ P') :
-- imply
  P ∆ P' ⊆ M ∧ sources ends (P ∆ P') = sources ends P ∆ sources ends P' ∧ #(P ∆ P') < #P + #P' := by
-- proof
  apply StatMech.Walls.gc2_splice_surgery ends M P P' hPM hP'M hiP hiP'

/--
[gc2_Kedge_even_in_Mcomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_core.lean)
-/
@[path]
private lemma gc2_Kedge_even_in_Mcomp_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M K : Finset ι}
  {w : V}
  {i : ι}
-- given
  (hKM : K ⊆ M)
  (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag)
  (hi : i ∈ K) :
-- imply
  Even (#((compOf ends M w).filter (fun x => x ∈ ends i))) := by
-- proof
  apply StatMech.Walls.gc2_Kedge_even_in_Mcomp ends M K hKM hnd w hi

/--
[gc2_K_exists_imp_FB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_core.lean)
-/
@[path]
private lemma gc2_K_exists_imp_FB_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M K : Finset ι}
  {B : Finset V}
-- given
  (hKM : K ⊆ M)
  (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag)
  (hKsrc : sources ends K = B) :
-- imply
  gc2_FB ends M B := by
-- proof
  apply StatMech.Walls.gc2_K_exists_imp_FB ends M K hKM hnd hKsrc

/--
[gc2_count_B_eq_count_empty_of_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_core.lean)
-/
@[path]
private lemma gc2_count_B_eq_count_empty_of_K_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M K : Finset ι}
  {B : Finset V}
-- given
  (hKM : K ⊆ M)
  (hKsrc : sources ends K = B) :
-- imply
  #(M.powerset.filter (fun N => sources ends N = B)) = #(M.powerset.filter (fun N => sources ends N = ∅)) := by
-- proof
  apply StatMech.Walls.gc2_count_B_eq_count_empty_of_K ends M K hKM hKsrc

/--
[gc2_eq_swi_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_core.lean)
-/
@[path]
private lemma gc2_eq_swi_count_eq
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
  apply StatMech.Walls.gc2_eq_swi_count ends M hnd B

/--
[gc2_minlenDisjoint_K_exists_current](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_core.lean)
-/
@[path]
private lemma gc2_minlenDisjoint_K_exists_current_eq
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
  {B : Finset W}
-- given
  (hFB : gc2_FB (endsM G m) M B) :
-- imply
  ∃ K ⊆ M, RandomCurrent.sources (endsM G m) K = B := by
-- proof
  apply StatMech.Walls.gc2_minlenDisjoint_K_exists_current G m M B hFB

/--
[gc2_eq_swi_count_current](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_core.lean)
-/
@[path]
private lemma gc2_eq_swi_count_current_eq
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
  apply StatMech.Walls.gc2_eq_swi_count_current G m M B

/--
[gc2_eq_swi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc2_core.lean)
-/
@[path]
private lemma gc2_eq_swi_eq
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
  apply StatMech.Walls.gc2_eq_swi G m B


-- created on 2026-10-23
