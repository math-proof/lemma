/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part25
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagMerge_slice_terminal_order {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hterm : ¬zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    zagMergeOrder (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε)
      (zagSliceTerminalTriple e π ε hε hterm) = e := by
  simpa only [zagMergeOrder, zagSliceTerminalTriple] using
    zagSlice_merge_order e π ε hε

theorem zagMerge_slice_terminal_vertical {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hterm : ¬zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    zagMergeVertical (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε)
      (zagSliceTerminalTriple e π ε hε hterm) = π := by
  simpa only [zagMergeVertical, zagSliceTerminalTriple] using
    zagSlice_merge_vertical e π ε hε

theorem zagMerge_slice_terminal_point {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hterm : ¬zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    zagMergePoint (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε)
      (zagSliceTerminalTriple e π ε hε hterm) = ε := by
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  let m := zagSliceTerminalTriple e π ε hε hterm
  have hv : zagMergeVertical e' π' m = π :=
    zagMerge_slice_terminal_vertical e π ε hε hterm
  have hl : e' m.third = π ε := by
    change zagSliceOrder e π ε hε (zagCutPos e π ε hε) = π ε
    exact zagSliceOrder_apply_right e π ε hε
  change (zagMergeVertical e' π' m).symm (e' m.third) = ε
  rw [hv, hl, π.symm_apply_apply]

theorem zagResidualMerge_slice_order {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    zagResidualMergeOrder (zagSliceOrder e π ε hε)
      (zagSliceVertical e π ε hε)
      (zagSliceResidualTriple e π ε hε hres) ε hres
      (zagSliceResidualTriple_third e π ε hε hres) = e := by
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  let l := zagCutPos e π ε hε
  have hlast : e'.symm (π' ε) = l := by
    apply e'.injective
    rw [e'.apply_symm_apply]
    exact (zagSlice_residual_apply e π ε hε hres).trans
      (zagSliceOrder_apply_right e π ε hε).symm
  simp only [zagResidualMergeOrder, zagSliceResidualTriple]
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let hij := zagNTAE_min_lt_image e π hε
  let hjl := zagImage_lt_cutPos e π ε hε
  let q := zagBlockMiddle i j l hij hjl
  have hiq : i < q := (zagBlockMiddle_bounds i j l hij hjl).1
  have hql : q < l := (zagBlockMiddle_bounds i j l hij hjl).2
  have hqactual : q < e'.symm (π' ε) := by rw [hlast]; exact hql
  have hB : zagBlockSwap i q (e'.symm (π' ε)) hiq hqactual =
      zagBlockSwap i q l hiq hql :=
    zagBlockSwap_congr_right i q (e'.symm (π' ε)) l
      hiq hqactual hql hlast
  rw [hB]
  exact zagSlice_merge_order e π ε hε

theorem zagResidualMerge_slice_vertical {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    zagResidualMergeVertical (zagSliceOrder e π ε hε)
      (zagSliceVertical e π ε hε)
      (zagSliceResidualTriple e π ε hε hres) ε = π := by
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  let i := zagCycleMinPos e π ε
  let l := zagCutPos e π ε hε
  let j := e.symm (π ε)
  let q := zagBlockMiddle i j l (zagNTAE_min_lt_image e π hε)
    (zagImage_lt_cutPos e π ε hε)
  have hpoint : π' ε = π ε := zagSlice_residual_apply e π ε hε hres
  have hright : e' l = π ε := zagSliceOrder_apply_right e π ε hε
  change π' * zagTriangle (e' i) (e' q) (π' ε) = π
  rw [hpoint, ← hright]
  exact zagSlice_merge_vertical e π ε hε

theorem zagSliceStep_mergeStep_terminal {n : ℕ} (p : ZagMarkedPlane n) :
    zagSliceStep (zagMergeStep (Sum.inl p)) = Sum.inl p := by
  rcases p with ⟨e, π, m⟩
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let hε := zagMergePoint_nontrivialAntiExceedance e π m
  have he : zagSliceOrder e' π' ε hε = e :=
    zagSlice_merge_order_from_marked e π m
  have hπ : zagSliceVertical e' π' ε hε = π :=
    zagSlice_merge_vertical_from_marked e π m
  have hterm : ¬zagNontrivialAntiExceedance
      (zagSliceOrder e' π' ε hε) (zagSliceVertical e' π' ε hε) ε := by
    intro hres
    apply zagMergePoint_not_nontrivialAntiExceedance e π m
    simpa only [he, hπ] using hres
  have hset :
      (zagSliceTerminalTriple e' π' ε hε hterm).toFinset = m.toFinset :=
    (zagSliceTerminalTriple_toFinset e' π' ε hε hterm).trans
      (zagSlice_merge_marked_from_marked e π m)
  have hm : HEq (zagSliceTerminalTriple e' π' ε hε hterm) m :=
    zagMarkedTriple_heq_of_toFinset he hπ hset
  have hp : ZagMarkedPlane.mk (zagSliceOrder e' π' ε hε)
      (zagSliceVertical e' π' ε hε)
      (zagSliceTerminalTriple e' π' ε hε hterm) =
      ZagMarkedPlane.mk e π m :=
    zagMarkedPlane_ext he hπ hm
  change zagSliceStep ⟨e', π', ε, hε⟩ = Sum.inl ⟨e, π, m⟩
  simp only [zagSliceStep, hterm]
  exact congrArg Sum.inl hp

theorem zagSliceStep_mergeStep_residual {n : ℕ}
    (p : ZagResidualMarkedPlane n) :
    zagSliceStep (zagMergeStep (Sum.inr p)) = Sum.inr p := by
  rcases p with ⟨e, π, m, ε, hε, hthird⟩
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let hε' := zagResidualMergePoint_nontrivialAntiExceedance
    e π m ε hε hthird
  have he : zagSliceOrder e' π' ε hε' = e :=
    zagResidualSlice_merge_order e π m ε hε hthird
  have hπ : zagSliceVertical e' π' ε hε' = π :=
    zagResidualSlice_merge_vertical e π m ε hε hthird
  have hres : zagNontrivialAntiExceedance
      (zagSliceOrder e' π' ε hε') (zagSliceVertical e' π' ε hε') ε := by
    simpa only [he, hπ] using hε
  have hset :
      (zagSliceResidualTriple e' π' ε hε' hres).toFinset = m.toFinset :=
    (zagSliceResidualTriple_toFinset e' π' ε hε' hres).trans
      (zagResidualSlice_merge_marked e π m ε hε hthird)
  have hm : HEq (zagSliceResidualTriple e' π' ε hε' hres) m :=
    zagMarkedTriple_heq_of_toFinset he hπ hset
  have hp : ZagResidualMarkedPlane.mk (zagSliceOrder e' π' ε hε')
      (zagSliceVertical e' π' ε hε')
      (zagSliceResidualTriple e' π' ε hε' hres) ε hres
      (zagSliceResidualTriple_third e' π' ε hε' hres) =
      ZagResidualMarkedPlane.mk e π m ε hε hthird :=
    zagResidualMarkedPlane_ext he hπ hm rfl
  change zagSliceStep ⟨e', π', ε, hε'⟩ =
    Sum.inr ⟨e, π, m, ε, hε, hthird⟩
  simp only [zagSliceStep, hres]
  exact congrArg Sum.inr hp

end MetaMathlibExt
