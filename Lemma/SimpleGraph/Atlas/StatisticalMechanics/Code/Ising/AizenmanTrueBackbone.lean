import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.AizenmanTrueBackbone.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Ising


/--
[atb_conn_iff_mem_backbone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean)
-/
@[path]
private lemma atb_conn_iff_mem_backbone_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o z : V} :
-- imply
  connK ends m o z ↔ z ∈ atb_backbone ends m o := by
-- proof
  apply StatMech.Ising.atb_conn_iff_mem_backbone ends m o z

/--
[atb_conn_xy_of_mem_backbone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean)
-/
@[path]
private lemma atb_conn_xy_of_mem_backbone_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hx : x ∈ atb_backbone ends m o)
  (hy : y ∈ atb_backbone ends m o) :
-- imply
  connK ends m x y := by
-- proof
  apply StatMech.Ising.atb_conn_xy_of_mem_backbone ends m hx hy

/--
[atb_allConn_of_xy_in_backbone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean)
-/
@[path]
private lemma atb_allConn_of_xy_in_backbone_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hx : x ∈ atb_backbone ends m o)
  (hy : y ∈ atb_backbone ends m o) :
-- imply
  aie_allConn ends m o x y := by
-- proof
  apply StatMech.Ising.atb_allConn_of_xy_in_backbone ends m hx hy

/--
[atb_allConn_iff_xy_in_backbone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean)
-/
@[path]
private lemma atb_allConn_iff_xy_in_backbone_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V} :
-- imply
  aie_allConn ends m o x y ↔ (x ∈ atb_backbone ends m o ∧ y ∈ atb_backbone ends m o) := by
-- proof
  apply StatMech.Ising.atb_allConn_iff_xy_in_backbone ends m o x y

/--
[atb_signDominance_per_backbone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean)
-/
@[path]
private lemma atb_signDominance_per_backbone_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {u v : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : srcK ends m = A)
  (huv : u ≠ v)
  (hφnn : ∀ K, 0 ≤ φ K)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
-- imply
  aie_mass ends m φ (A ∆ {u, v}) ≤ aie_mass ends m φ A := by
-- proof
  apply StatMech.Ising.atb_signDominance_per_backbone ends m hnd A hm huv φ hφnn hφ

/--
[atb_conditioned_gap_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean)
-/
@[path]
private lemma atb_conditioned_gap_eq_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {o x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : srcK ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K) :
-- imply
  aie_gap ends m φ A o x y = aie_mass ends m φ A * asd_ghsBackboneFactor ends m o x y := by
-- proof
  apply StatMech.Ising.atb_conditioned_gap_eq ends m hnd A hm hox hoy hxy φ hφ

/--
[atb_conditioned_gap_allBackbone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean)
-/
@[path]
private lemma atb_conditioned_gap_allBackbone_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {A : Finset V}
  {o x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : srcK ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hφ : ∀ K P, P ⊆ m → K ⊆ m → φ (K ∆ P) = φ K)
  (hx : x ∈ atb_backbone ends m o)
  (hy : y ∈ atb_backbone ends m o) :
-- imply
  aie_gap ends m φ A o x y = -2 * aie_mass ends m φ A := by
-- proof
  apply StatMech.Ising.atb_conditioned_gap_allBackbone ends m hnd A hm hox hoy hxy φ hφ hx hy

/--
[atb_conditioned_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean)
-/
@[path]
private lemma atb_conditioned_decomp_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset (Finset ι)}
  {A : Finset V}
  {o x y : V}
  {Φ : Finset ι → Finset ι → ℝ}
-- given
  (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : ∀ m ∈ M, srcK ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K) :
-- imply
  ∑ m ∈ M, aie_gap ends m (Φ m) A o x y = (∑ m ∈ M.filter (fun m => aie_noneConn ends m o x y), aie_mass ends m (Φ m) A) - 2 * (∑ m ∈ M.filter (fun m => aie_allConn ends m o x y), aie_mass ends m (Φ m) A) := by
-- proof
  apply StatMech.Ising.atb_conditioned_decomp ends M hnd A hm hox hoy hxy Φ hΦ

/--
[atb_conditionedDom_holds_of_no_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean)
-/
@[path]
private lemma atb_conditionedDom_holds_of_no_allConn_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset (Finset ι)}
  {A : Finset V}
  {o x y : V}
  {Φ : Finset ι → Finset ι → ℝ}
-- given
  (hΦnn : ∀ m K, 0 ≤ (Φ m) K)
  (hno : M.filter (fun m => aie_allConn ends m o x y) = ∅) :
-- imply
  atb_conditionedDom ends M A o x y Φ := by
-- proof
  apply StatMech.Ising.atb_conditionedDom_holds_of_no_allConn ends M A Φ hΦnn hno

/--
[atb_conditioned_closure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean)
-/
@[path]
private lemma atb_conditioned_closure_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {M : Finset (Finset ι)}
  {A : Finset V}
  {o x y : V}
  {Φ : Finset ι → Finset ι → ℝ}
-- given
  (hnd : ∀ m ∈ M, ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : ∀ m ∈ M, srcK ends m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hΦ : ∀ m ∈ M, ∀ K P, P ⊆ m → K ⊆ m → (Φ m) (K ∆ P) = (Φ m) K)
  (hdom : atb_conditionedDom ends M A o x y Φ) :
-- imply
  0 ≤ ∑ m ∈ M, aie_gap ends m (Φ m) A o x y := by
-- proof
  apply StatMech.Ising.atb_conditioned_closure ends M hnd A hm hox hoy hxy Φ hΦ hdom

/--
[atb_tri_x_in_backbone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean)
-/
@[path]
private lemma atb_tri_x_in_backbone_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  (1 : Fin 3) ∈ atb_backbone ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 := by
-- proof
  apply StatMech.Ising.atb_tri_x_in_backbone

/--
[atb_tri_y_in_backbone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean)
-/
@[path]
private lemma atb_tri_y_in_backbone_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  (2 : Fin 3) ∈ atb_backbone ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 0 := by
-- proof
  apply StatMech.Ising.atb_tri_y_in_backbone

/--
[atb_conditionedDom_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanTrueBackbone.lean)
-/
@[path]
private lemma atb_conditionedDom_refutable_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  ¬ atb_conditionedDom ahd_triEnds ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) (srcK ahd_triEnds ({0, 1, 2} : Finset (Fin 3))) 0 1 2 (fun _ _ => 1) := by
-- proof
  apply StatMech.Ising.atb_conditionedDom_refutable


-- created on 2026-10-23
