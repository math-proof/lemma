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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part24
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagSliceResidualTriple_third {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    zagCycleMinPos (zagSliceOrder e π ε hε)
      (zagSliceVertical e π ε hε) ε =
        (zagSliceResidualTriple e π ε hε hres).third :=
  rfl

theorem zagSliceTerminalTriple_toFinset {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hterm : ¬zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    (zagSliceTerminalTriple e π ε hε hterm).toFinset =
      zagSliceMarked e π ε hε := by
  have hs := zagSliceMarked_eq_terminal e π ε hε hterm
  dsimp only at hs
  simpa only [zagSliceTerminalTriple, ZagMarkedTriple.toFinset] using hs.symm

theorem zagSliceResidualTriple_toFinset {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    (zagSliceResidualTriple e π ε hε hres).toFinset =
      zagSliceMarked e π ε hε := by
  have hs := zagSliceMarked_eq_residual e π ε hε hres
  dsimp only at hs
  simpa only [zagSliceResidualTriple, ZagMarkedTriple.toFinset] using hs.symm

end MetaMathlibExt
