/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HilbertWaring.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Def.Combinatorics.Schnirelmann
import Lemma.Finset.Schnirelmann
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.PSeries
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic
import Def.NumberTheory.HilbertWaring.Part2
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/


namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

@[simp] lemma hw_signedVal_natAbs (H : ℕ) (h : hwSigned H) :
    (hwSignedVal H h).natAbs = h.2.val + 1 := by
  rcases h with ⟨s, i⟩
  fin_cases s
  · change (((i.val + 1 : ℕ) : ℤ)).natAbs = i.val + 1
    exact Int.natAbs_natCast _
  · change (-((i.val + 1 : ℕ) : ℤ)).natAbs = i.val + 1
    rw [Int.natAbs_neg]
    exact Int.natAbs_natCast _

lemma hw_signedVal_ne_zero (H : ℕ) (h : hwSigned H) : hwSignedVal H h ≠ 0 := by
  apply Int.natAbs_pos.mp
  rw [hw_signedVal_natAbs]
  omega

end MathlibExt.NumberTheory.HilbertWaringWanted
