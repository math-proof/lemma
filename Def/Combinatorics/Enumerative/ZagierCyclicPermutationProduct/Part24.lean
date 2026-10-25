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
import Theorem.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part23
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def zagSliceTerminalTriple {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hterm : ¬zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    ZagMarkedTriple (zagSliceOrder e π ε hε)
      (zagSliceVertical e π ε hε) := by
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij := zagNTAE_min_lt_image e π hε
  let hjl := zagImage_lt_cutPos e π ε hε
  let q := zagBlockMiddle i j l hij hjl
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  exact {
    first := i
    middle := q
    third := l
    first_mem := by
      rw [zag_mem_cycleMinima_iff]
      change zagCycleMinPos e' π' (e' i) = i
      rw [show e' i = e i by exact zagSliceOrder_apply_left e π ε hε]
      exact zagSlice_cycleMinPos_left e π ε hε
    middle_mem := by
      rw [zag_mem_cycleMinima_iff]
      change zagCycleMinPos e' π' (e' q) = q
      rw [show e' q = e l by exact zagSliceOrder_apply_middle e π ε hε]
      exact zagSlice_cycleMinPos_middle e π ε hε
    third_mem := by
      rw [zag_mem_cycleMinima_iff]
      change zagCycleMinPos e' π' (e' l) = l
      rw [show e' l = π ε by exact zagSliceOrder_apply_right e π ε hε]
      exact zagSlice_terminal_cycleMinPos_right e π ε hε hterm
    first_lt_middle := (zagBlockMiddle_bounds i j l hij hjl).1
    middle_lt_third := (zagBlockMiddle_bounds i j l hij hjl).2
  }

noncomputable def zagSliceResidualTriple {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    ZagMarkedTriple (zagSliceOrder e π ε hε)
      (zagSliceVertical e π ε hε) := by
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij := zagNTAE_min_lt_image e π hε
  let hjl := zagImage_lt_cutPos e π ε hε
  let q := zagBlockMiddle i j l hij hjl
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  let d := zagCycleMinPos e' π' ε
  exact {
    first := i
    middle := q
    third := d
    first_mem := by
      rw [zag_mem_cycleMinima_iff]
      change zagCycleMinPos e' π' (e' i) = i
      rw [show e' i = e i by exact zagSliceOrder_apply_left e π ε hε]
      exact zagSlice_cycleMinPos_left e π ε hε
    middle_mem := by
      rw [zag_mem_cycleMinima_iff]
      change zagCycleMinPos e' π' (e' q) = q
      rw [show e' q = e l by exact zagSliceOrder_apply_middle e π ε hε]
      exact zagSlice_cycleMinPos_middle e π ε hε
    third_mem := zag_cycleMinPos_mem_cycleMinima e' π' ε
    first_lt_middle := (zagBlockMiddle_bounds i j l hij hjl).1
    middle_lt_third := zagSlice_residual_min_gt_middle e π ε hε hres
  }

end MetaMathlibExt
