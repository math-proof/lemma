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
import Def.NumberTheory.HilbertWaring.Part10
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/


namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

lemma hw_blockQuadMap_mem (k r N M : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ)
    (hm : ∀ z : hwBlockChoice r N, (hwBlockChoiceDiff k r N hk a z).natAbs ≤ M)
    {u : Fin 4 → hwBlockChoice r N}
    (hu : u ∈ hwZeroQuadruples (hwBlockChoiceFreq k r N hk a)) :
    hwBlockQuadMap k r N M hk a hm u ∈ hwCenteredFourNonzero N M := by
  have hzero : ∑ i, hwBlockChoiceFreq k r N hk a (u i) = 0 :=
    (Finset.mem_filter.mp hu).2
  simp only [hwCenteredFourNonzero, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · simp only [hwBlockQuadMap, hw_centered_signedToCentered, hw_centered_toCentered]
    simpa [hwBlockChoiceFreq] using hzero
  · intro i
    simp only [hwBlockQuadMap, hw_centered_signedToCentered]
    exact hw_signedVal_ne_zero N (u i).1

lemma hw_blockQuadMap_image_card_le (k r N M : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ)
    (hm : ∀ z : hwBlockChoice r N, (hwBlockChoiceDiff k r N hk a z).natAbs ≤ M) :
    #((hwZeroQuadruples (hwBlockChoiceFreq k r N hk a)).image
        (hwBlockQuadMap k r N M hk a hm)) ≤ hwFourTermCount N M := by
  calc
    #((hwZeroQuadruples (hwBlockChoiceFreq k r N hk a)).image
        (hwBlockQuadMap k r N M hk a hm)) ≤ #(hwCenteredFourNonzero N M) := by
      apply Finset.card_le_card
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨u, hu, rfl⟩
      exact hw_blockQuadMap_mem k r N M hk a hm hu
    _ ≤ hwFourTermCount N M := hw_centeredFourNonzero_card_le N M

end MathlibExt.NumberTheory.HilbertWaringWanted
