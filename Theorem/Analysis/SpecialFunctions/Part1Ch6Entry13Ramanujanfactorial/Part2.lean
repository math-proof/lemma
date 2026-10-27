/-
Author: @akiezun, Avocado
-/

import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
import Def.Analysis.SpecialFunctions.Part1Ch6Entry13Ramanujanfactorial.Part2
/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 13

Two series in powers of x are summable and equal for |x|>1.
-/


namespace Ramanujan.Part1Ch6

namespace Entry13Ramanujanfactorial

open scoped Nat Real BigOperators Interval Polynomial

open Asymptotics Filter Finset Complex Topology

noncomputable section

theorem dblR_summable {t : ℝ} (ht : ‖t‖ < 1) : Summable (dblR t) := by
  have hL := dblL_summable ht
  have hLn := hL.norm
  have hmaj : Summable (fun c : ℕ+ × ℕ+ => 2 * ‖dblL t c‖) := hLn.mul_left 2
  apply Summable.of_norm_bounded hmaj
  intro c
  simp only [dblR]
  by_cases hC : (c.2:ℕ) % 2 = (c.1:ℕ) % 2 ∧ (c.1:ℕ) ≤ (c.2:ℕ)
  · rw [ite_eq_left hC]
    by_cases hE : (c.1:ℕ) = (c.2:ℕ)
    · rw [ite_eq_left hE]
      have heq : signW c.1 * t ^ ((c.1:ℕ)*(c.2:ℕ)) = dblL t c := rfl
      rw [heq]
      have hnn := norm_nonneg (dblL t c)
      linarith
    · rw [ite_eq_right hE]
      have hD : ‖dblL t c‖ = ‖t ^ ((c.1:ℕ)*(c.2:ℕ))‖ := by
        simp only [dblL, signW, norm_mul]
        simp
      have h2n : ‖(2:ℝ)‖ = 2 := by
        rw [Real.norm_eq_abs]
        norm_num
      have hsn : ‖signW c.1‖ = 1 := by simp [signW]
      have hR : ‖(2:ℝ) * signW c.1 * t ^ ((c.1:ℕ)*(c.2:ℕ))‖
          = 2 * ‖t ^ ((c.1:ℕ)*(c.2:ℕ))‖ := by
        calc ‖(2:ℝ) * signW c.1 * t ^ ((c.1:ℕ)*(c.2:ℕ))‖
            = ‖(2:ℝ)‖ * ‖signW c.1‖ * ‖t ^ ((c.1:ℕ)*(c.2:ℕ))‖ := by
              rw [norm_mul, norm_mul]
          _ = 2 * ‖t ^ ((c.1:ℕ)*(c.2:ℕ))‖ := by rw [h2n, hsn, mul_one]
      rw [hR, hD]
  · rw [ite_eq_right hC]
    simp only [norm_zero]
    have hnn := norm_nonneg (dblL t c)
    linarith

theorem dblR_zero (t : ℝ) (k : ℕ+) :
    dblR t (k, ((arithEquiv k) 0).val) = signW k * t ^ ((k:ℕ)^2) := by
  have h0 : (((arithEquiv k) 0).val : ℕ+) = k := by
    simp only [arithEquiv]
    apply PNat.eq
    simp
  rw [h0]
  simp only [dblR]
  simp only [le_refl, and_self]
  simp only [ite_true]
  congr 1
  congr 1
  rw [pow_two]

theorem dblR_succ (t : ℝ) (k : ℕ+) (m : ℕ) :
    dblR t (k, ((arithEquiv k) (m+1)).val)
      = 2 * signW k * t ^ ((k:ℕ) * ((k:ℕ) + 2 * (m+1))) := by
  have hC1 : ((((arithEquiv k) (m+1)).val : ℕ+) : ℕ) % 2 = (k:ℕ) % 2 := by
    show ((k:ℕ) + 2 * (m+1)) % 2 = (k:ℕ) % 2
    omega
  have hC2 : (k:ℕ) ≤ ((((arithEquiv k) (m+1)).val : ℕ+) : ℕ) := by
    show (k:ℕ) ≤ (k:ℕ) + 2 * (m+1)
    omega
  have hne : (k:ℕ) ≠ ((((arithEquiv k) (m+1)).val : ℕ+) : ℕ) := by
    show (k:ℕ) ≠ (k:ℕ) + 2 * (m+1)
    omega
  have hexp : (k:ℕ) * ((((arithEquiv k) (m+1)).val : ℕ+) : ℕ)
      = (k:ℕ) * ((k:ℕ) + 2 * (m+1)) := by
    show (k:ℕ) * ((k:ℕ) + 2 * (m+1)) = _
    rfl
  simp only [dblR]
  rw [ite_eq_left ⟨hC1, hC2⟩]
  rw [ite_eq_right hne]
  rw [hexp]

theorem dblR_fiber_support (t : ℝ) (k : ℕ+) :
    Function.support (fun j : ℕ+ => dblR t (k, j))
      ⊆ { j : ℕ+ | (j:ℕ) % 2 = (k:ℕ) % 2 ∧ (k:ℕ) ≤ (j:ℕ) } := by
  intro j hj
  simp only [Function.support, ne_eq] at hj
  show (j:ℕ) % 2 = (k:ℕ) % 2 ∧ (k:ℕ) ≤ (j:ℕ)
  by_contra hcon
  have h0 : dblR t (k, j) = 0 := by
    simp only [dblR]
    rw [ite_eq_right]
    exact hcon
  exact hj h0

theorem per_k_R {t : ℝ} (ht : ‖t‖ < 1) (k : ℕ+) :
    ∑' j : ℕ+, dblR t (k, j) = singleR t k := by
  have hRsumm := dblR_summable ht
  have e1 : (∑' j : ℕ+, dblR t (k, j))
      = ∑' jm : { j : ℕ+ // (j:ℕ) % 2 = (k:ℕ) % 2 ∧ (k:ℕ) ≤ (j:ℕ) },
          dblR t (k, jm.val) := by
    have hsup := dblR_fiber_support t k
    have h := tsum_subtype_eq_of_support_subset (f := fun j : ℕ+ => dblR t (k, j))
      (s := { j : ℕ+ | (j:ℕ) % 2 = (k:ℕ) % 2 ∧ (k:ℕ) ≤ (j:ℕ) }) hsup
    exact h.symm
  have e2 : (∑' jm : { j : ℕ+ // (j:ℕ) % 2 = (k:ℕ) % 2 ∧ (k:ℕ) ≤ (j:ℕ) },
          dblR t (k, jm.val))
      = ∑' m : ℕ, dblR t (k, ((arithEquiv k) m).val) := by
    have h := (arithEquiv k).tsum_eq (f := fun jm : { j : ℕ+ // _ } => dblR t (k, jm.val))
    exact h.symm
  rw [e1, e2]
  have hfibM : Summable (fun m : ℕ => dblR t (k, ((arithEquiv k) m).val)) := by
    apply hRsumm.comp_injective
    intro a b hab
    have hval : (((arithEquiv k) a).val : ℕ+) = (((arithEquiv k) b).val : ℕ+) :=
      congrArg Prod.snd hab
    have := (arithEquiv k).injective (Subtype.ext hval)
    exact this
  rw [hfibM.tsum_eq_zero_add]
  rw [dblR_zero]
  have htail_eq : ∀ m : ℕ, dblR t (k, ((arithEquiv k) (m+1)).val)
      = (2 * signW k * t ^ ((k:ℕ)^2 + 2*(k:ℕ))) * (t ^ (2*(k:ℕ))) ^ m := by
    intro m
    rw [dblR_succ]
    have hexp : (k:ℕ) * ((k:ℕ) + 2 * (m+1)) = ((k:ℕ)^2 + 2*(k:ℕ)) + m * (2*(k:ℕ)) := by
      ring
    rw [hexp, pow_add, pow_mul]
    ring
  simp only [htail_eq]
  rw [tsum_mul_left]
  have hkpos : 0 < (k:ℕ) := k.2
  have h2k : 2 * (k:ℕ) ≠ 0 := by omega
  have htk2 : ‖t ^ (2*(k:ℕ))‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) ht h2k
  have hgeo := tsum_geometric_of_norm_lt_one (K := ℝ) (ξ := t ^ (2*(k:ℕ))) htk2
  rw [hgeo]
  simp only [singleR]
  have hR_ne : (1:ℝ) - t ^ (2*(k:ℕ)) ≠ 0 := by
    intro h
    have h1 : t ^ (2*(k:ℕ)) = 1 := by linarith
    have hn : ‖t ^ (2*(k:ℕ))‖ = 1 := by rw [h1, norm_one]
    linarith [htk2]
  have hAB : t ^ ((k:ℕ)^2) * t ^ (2*(k:ℕ)) = t ^ ((k:ℕ)^2 + 2*(k:ℕ)) := by
    rw [← pow_add]
  field_simp
  linear_combination (-2 * signW k) * hAB

end
end Entry13Ramanujanfactorial
end Ramanujan.Part1Ch6
