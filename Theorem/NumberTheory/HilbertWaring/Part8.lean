module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Def.Combinatorics.Schnirelmann
public import Theorem.Finset.Schnirelmann
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.PSeries
public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic
public import Def.NumberTheory.HilbertWaring.Part11


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HilbertWaring.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/
namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

lemma hw_zeroQuadruples_card_le (k r N M A : ℕ) (hk : 0 < k)
    (a : Fin (k + 1) → ℤ)
    (hm : ∀ z : hwBlockChoice r N, (hwBlockChoiceDiff k r N hk a z).natAbs ≤ M)
    (hA : ∀ h : hwSigned N,
      #(hwMomentFinset r N
        (hwPolyEval (k - 1) (hwDiffCoeffs k hk a (h.2.val + 1)))) ≤ A) :
    #(hwZeroQuadruples (hwBlockChoiceFreq k r N hk a)) ≤
      hwFourTermCount N M * A ^ 4 := by
  let S := hwZeroQuadruples (hwBlockChoiceFreq k r N hk a)
  let f := hwBlockQuadMap k r N M hk a hm
  have hmap : Set.MapsTo f (↑S) (↑(S.image f)) := by
    intro u hu
    exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  change #S ≤ _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    (∑ b ∈ S.image f, #{u ∈ S | f u = b}) ≤
        ∑ _b ∈ S.image f, A ^ 4 := by
      gcongr with b
      exact hw_blockQuadMap_fiber_card_le k r N M A hk a hm hA b
    _ = #(S.image f) * A ^ 4 := by simp
    _ ≤ hwFourTermCount N M * A ^ 4 := by
      gcongr
      exact hw_blockQuadMap_image_card_le k r N M hk a hm

end MathlibExt.NumberTheory.HilbertWaringWanted
