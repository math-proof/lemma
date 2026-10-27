import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.AizenmanResum.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Ising


/--
[ght_backbone_removed_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanResum.lean)
-/
@[path]
private lemma ght_backbone_removed_subset_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {m P : Finset ι}
-- given
  (hP : P ⊆ m) :
-- imply
  m ∆ P ⊆ m := by
-- proof
  apply StatMech.Ising.ght_backbone_removed_subset m P hP

/--
[ght_backbone_removed_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanResum.lean)
-/
@[path]
private lemma ght_backbone_removed_sources_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m P : Finset ι}
  {A : Finset V}
  {x y : V}
-- given
  (hm : srcK ends m = A)
  (hPsrc : srcK ends P = {x, y}) :
-- imply
  srcK ends (m ∆ P) = A ∆ {x, y} := by
-- proof
  apply StatMech.Ising.ght_backbone_removed_sources ends m P A hm hPsrc

/--
[ght_backbone_exists_xy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanResum.lean)
-/
@[path]
private lemma ght_backbone_exists_xy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o x y : V}
-- given
  (hall : aie_allConn ends m o x y)
  (hxy : x ≠ y) :
-- imply
  ∃ P ⊆ m, srcK ends P = {x, y} := by
-- proof
  apply StatMech.Ising.ght_backbone_exists_xy ends m hall hxy

/--
[ght_backbone_removed_nd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanResum.lean)
-/
@[path]
private lemma ght_backbone_removed_nd_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m P : Finset ι}
-- given
  (hP : P ⊆ m)
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) :
-- imply
  ∀ i ∈ m ∆ P, ¬ (ends i).IsDiag := by
-- proof
  apply StatMech.Ising.ght_backbone_removed_nd ends m P hP hnd

/--
[ght_backbone_per_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanResum.lean)
-/
@[path]
private lemma ght_backbone_per_switching_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m P : Finset ι}
  {A : Finset V}
  {x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hP : P ⊆ m)
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : srcK ends m = A)
  (hPsrc : srcK ends P = {x, y})
  (hxy : x ≠ y)
  (hφ : ∀ K Q, Q ⊆ m ∆ P → K ⊆ m ∆ P → φ (K ∆ Q) = φ K) :
-- imply
  aie_mass ends (m ∆ P) φ A = (if connK ends (m ∆ P) x y then 1 else 0) * aie_mass ends (m ∆ P) φ (A ∆ {x, y}) := by
-- proof
  apply StatMech.Ising.ght_backbone_per_switching ends m P hP hnd A hm hPsrc hxy φ hφ

/--
[ght_backbone_no_surplus_of_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanResum.lean)
-/
@[path]
private lemma ght_backbone_no_surplus_of_conn_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m P : Finset ι}
  {A : Finset V}
  {x y : V}
  {φ : Finset ι → ℝ}
-- given
  (hP : P ⊆ m)
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : srcK ends m = A)
  (hPsrc : srcK ends P = {x, y})
  (hxy : x ≠ y)
  (hφ : ∀ K Q, Q ⊆ m ∆ P → K ⊆ m ∆ P → φ (K ∆ Q) = φ K)
  (hconn : connK ends (m ∆ P) x y) :
-- imply
  aie_mass ends (m ∆ P) φ (A ∆ {x, y}) = aie_mass ends (m ∆ P) φ A := by
-- proof
  apply StatMech.Ising.ght_backbone_no_surplus_of_conn ends m P hP hnd A hm hPsrc hxy φ hφ hconn

/--
[ght_backboneAvgDom_holds_of_no_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanResum.lean)
-/
@[path]
private lemma ght_backboneAvgDom_holds_of_no_allConn_eq
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
  (hno : M.filter (fun m => aie_allConn ends m o x y) = ∅) :
-- imply
  ght_backboneAvgDom ends M A o x y Φ := by
-- proof
  apply StatMech.Ising.ght_backboneAvgDom_holds_of_no_allConn ends M A Φ hno

/--
[ght_tri_backbones](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanResum.lean)
-/
@[path]
private lemma ght_tri_backbones_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  ght_backbones ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 1 2 = {{1}, {0, 2}} := by
-- proof
  apply StatMech.Ising.ght_tri_backbones

/--
[ght_tri_removed_conn_1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanResum.lean)
-/
@[path]
private lemma ght_tri_removed_conn_1_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  connK ahd_triEnds (({0, 1, 2} : Finset (Fin 3)) ∆ ({1} : Finset (Fin 3))) 1 2 := by
-- proof
  apply StatMech.Ising.ght_tri_removed_conn_1

/--
[ght_tri_removed_conn_2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanResum.lean)
-/
@[path]
private lemma ght_tri_removed_conn_2_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  connK ahd_triEnds (({0, 1, 2} : Finset (Fin 3)) ∆ ({0, 2} : Finset (Fin 3))) 1 2 := by
-- proof
  apply StatMech.Ising.ght_tri_removed_conn_2

/--
[ght_tri_resummed_filter_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanResum.lean)
-/
@[path]
private lemma ght_tri_resummed_filter_empty_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  (ght_backbones ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) 1 2).filter (fun P => aie_noneConn ahd_triEnds (({0, 1, 2} : Finset (Fin 3)) ∆ P) 0 1 2) = ∅ := by
-- proof
  apply StatMech.Ising.ght_tri_resummed_filter_empty

/--
[ght_tri_resummedNoneMass_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanResum.lean)
-/
@[path]
private lemma ght_tri_resummedNoneMass_zero_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  ght_resummedNoneMass ahd_triEnds ({0, 1, 2} : Finset (Fin 3)) (fun _ => 1) (srcK ahd_triEnds ({0, 1, 2} : Finset (Fin 3))) 0 1 2 = 0 := by
-- proof
  apply StatMech.Ising.ght_tri_resummedNoneMass_zero

/--
[ght_backboneAvgDom_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanResum.lean)
-/
@[path]
private lemma ght_backboneAvgDom_refutable_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι] :
-- imply
  ¬ ght_backboneAvgDom ahd_triEnds ({({0, 1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) (srcK ahd_triEnds ({0, 1, 2} : Finset (Fin 3))) 0 1 2 (fun _ _ => 1) := by
-- proof
  apply StatMech.Ising.ght_backboneAvgDom_refutable


-- created on 2026-10-23
