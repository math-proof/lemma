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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part21
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagSliceMarked_eq_terminal {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hterm : ¬zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    let i := zagCycleMinPos e π ε
    let j := e.symm (π ε)
    let l := zagCutPos e π ε hε
    let hij := zagNTAE_min_lt_image e π hε
    let hjl := zagImage_lt_cutPos e π ε hε
    zagSliceMarked e π ε hε =
      {i, zagBlockMiddle i j l hij hjl, l} := by
  dsimp only
  rw [zagSliceMarked]
  simp only [zagSlice_cycleMinPos_left,
    zagSlice_terminal_cycleMinPos_right e π ε hε hterm,
    zagSlice_cycleMinPos_middle]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem zagSliceMarked_eq_residual {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    let i := zagCycleMinPos e π ε
    let j := e.symm (π ε)
    let l := zagCutPos e π ε hε
    let hij := zagNTAE_min_lt_image e π hε
    let hjl := zagImage_lt_cutPos e π ε hε
    let e' := zagSliceOrder e π ε hε
    let π' := zagSliceVertical e π ε hε
    zagSliceMarked e π ε hε =
      {i, zagBlockMiddle i j l hij hjl, zagCycleMinPos e' π' ε} := by
  dsimp only
  rw [zagSliceMarked]
  have happ := zagSlice_residual_apply e π ε hε hres
  have hsame : (zagSliceVertical e π ε hε).SameCycle
      (π ε) ε := by
    have hs := (Equiv.Perm.SameCycle.rfl :
      (zagSliceVertical e π ε hε).SameCycle ε ε).apply_right
    simpa [happ] using hs.symm
  rw [zagSlice_cycleMinPos_left, zagSlice_cycleMinPos_middle,
    zagCycleMinPos_eq_of_sameCycle _ _ hsame]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem zagSlice_merge_order {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    let i := zagCycleMinPos e π ε
    let j := e.symm (π ε)
    let l := zagCutPos e π ε hε
    let hij := zagNTAE_min_lt_image e π hε
    let hjl := zagImage_lt_cutPos e π ε hε
    let q := zagBlockMiddle i j l hij hjl
    zagSliceOrder e π ε hε * zagBlockSwap i q l
        (zagBlockMiddle_bounds i j l hij hjl).1
        (zagBlockMiddle_bounds i j l hij hjl).2 = e := by
  dsimp only
  rw [zagSliceOrder, mul_assoc, zagBlockSwap_mul_reverse, mul_one]

theorem zagSlice_merge_vertical {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    let i := zagCycleMinPos e π ε
    let j := e.symm (π ε)
    let l := zagCutPos e π ε hε
    let hij := zagNTAE_min_lt_image e π hε
    let hjl := zagImage_lt_cutPos e π ε hε
    let q := zagBlockMiddle i j l hij hjl
    let e' := zagSliceOrder e π ε hε
    zagSliceVertical e π ε hε * zagTriangle (e' i) (e' q) (e' l) = π := by
  dsimp only
  let a := e (zagCycleMinPos e π ε)
  let b := π ε
  let c := e (zagCutPos e π ε hε)
  have hab : a ≠ b := fun h => by
    have hp := congrArg e.symm h
    have hlt := zagNTAE_min_lt_image e π hε
    exact (ne_of_lt hlt) (by simpa [a, b] using hp)
  have hac : a ≠ c := fun h => by
    have hp := congrArg e.symm h
    have h1 := zagNTAE_min_lt_image e π hε
    have h2 := zagImage_lt_cutPos e π ε hε
    simp only [a, c, e.symm_apply_apply] at hp
    omega
  have hbc : b ≠ c := fun h => by
    have hp := congrArg e.symm h
    have h2 := zagImage_lt_cutPos e π ε hε
    simp only [b, c, e.symm_apply_apply] at hp
    omega
  rw [zagSliceOrder_apply_left, zagSliceOrder_apply_middle,
    zagSliceOrder_apply_right]
  change (π * zagTriangle a b c) * zagTriangle a c b = π
  rw [mul_assoc, zagTriangle_mul_reverse hab hac hbc, mul_one]

theorem zagMarkedTriple_pairwise {n : ℕ}
    {e π : Equiv.Perm (Fin n)} (m : ZagMarkedTriple e π) :
    ¬π.SameCycle (e m.first) (e m.middle) ∧
      ¬π.SameCycle (e m.first) (e m.third) ∧
      ¬π.SameCycle (e m.middle) (e m.third) := by
  have hfirst := (zag_mem_cycleMinima_iff e π m.first).mp m.first_mem
  have hmiddle := (zag_mem_cycleMinima_iff e π m.middle).mp m.middle_mem
  have hthird := (zag_mem_cycleMinima_iff e π m.third).mp m.third_mem
  constructor
  · intro hsame
    have hmin := zagCycleMinPos_eq_of_sameCycle e π hsame
    rw [hfirst, hmiddle] at hmin
    exact m.first_lt_middle.ne hmin
  constructor
  · intro hsame
    have hmin := zagCycleMinPos_eq_of_sameCycle e π hsame
    rw [hfirst, hthird] at hmin
    exact (m.first_lt_middle.trans m.middle_lt_third).ne hmin
  · intro hsame
    have hmin := zagCycleMinPos_eq_of_sameCycle e π hsame
    rw [hmiddle, hthird] at hmin
    exact m.middle_lt_third.ne hmin

end MetaMathlibExt
