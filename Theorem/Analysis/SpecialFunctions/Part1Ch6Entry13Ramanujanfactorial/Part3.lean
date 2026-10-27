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
import Def.Analysis.SpecialFunctions.Part1Ch6Entry13Ramanujanfactorial.Part3
/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 13

Two series in powers of x are summable and equal for |x|>1.
-/


namespace Ramanujan.Part1Ch6

namespace Entry13Ramanujanfactorial

open scoped Nat Real BigOperators Interval Polynomial

open Asymptotics Filter Finset Complex Topology

noncomputable section

theorem finite_right (N : ℕ) (t : ℝ) :
    ∑ x ∈ N.divisorsAntidiagonal, (wR x * t^(x.1*x.2))
      = Rcoeff N * t^N := by
  simp only [Rcoeff]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  have hmem := Nat.mem_divisorsAntidiagonal.mp hx
  rw [hmem.1]

theorem hgx (t : ℝ) (N : ℕ+) (x : ↥((N:ℕ).divisorsAntidiagonal)) :
    dblR t (sigmaAntidiagonalEquivProd ⟨N, x⟩) = wR x.1 * t^(x.1.1*x.1.2) := by
  simp only [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, dblR, wR, signW,
    Equiv.coe_fn_mk, PNat.mk_coe]
  by_cases hC : x.1.2 % 2 = x.1.1 % 2 ∧ x.1.1 ≤ x.1.2
  · simp only [hC]
    by_cases hE : x.1.1 = x.1.2
    · simp [hE]
    · simp [hE]
  · simp [hC]

theorem right_tsum_eq {t : ℝ} (ht : ‖t‖ < 1) :
    ∑' c : ℕ+ × ℕ+, dblR t c
      = ∑' N : ℕ+, Rcoeff (N:ℕ) * t^((N:ℕ)) := by
  have hsum : Summable (dblR t) := dblR_summable ht
  have hsig : Summable ((dblR t) ∘ sigmaAntidiagonalEquivProd) :=
    (sigmaAntidiagonalEquivProd.summable_iff (f := dblR t)).mpr hsum
  have heq := sigmaAntidiagonalEquivProd.tsum_eq (f := dblR t)
  rw [← heq]
  have hsig2 : Summable (fun c : (N : ℕ+) × ↥((N:ℕ).divisorsAntidiagonal) ↦
      dblR t (sigmaAntidiagonalEquivProd c)) := hsig
  rw [Summable.tsum_sigma hsig2]
  refine tsum_congr fun N => ?_
  rw [tsum_fintype]
  have hstep : ∑ x : ↥((N:ℕ).divisorsAntidiagonal),
        dblR t (sigmaAntidiagonalEquivProd ⟨N, x⟩)
      = ∑ x ∈ (N:ℕ).divisorsAntidiagonal, (wR x * t^(x.1*x.2)) := by
    rw [← Finset.sum_attach ((N:ℕ).divisorsAntidiagonal)
      (fun p : ℕ × ℕ => wR p * t^(p.1*p.2))]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hgx]
  rw [hstep]
  exact finite_right (N:ℕ) t

theorem sign_odd (d : ℕ) (hd : Odd d) : (-1:ℝ)^(d+1) = 1 := by
  have h : Even (d+1) := hd.add_odd (by decide)
  exact h.neg_one_pow

theorem sign_even (d : ℕ) (hd : Even d) : (-1:ℝ)^(d+1) = -1 := by
  have h : Odd (d+1) := hd.add_odd (by decide)
  exact h.neg_one_pow

theorem sign_add_same (a b : ℕ) (h : a % 2 = b % 2) :
    (-1:ℝ)^(a+1) + (-1:ℝ)^(b+1) = 2 * (-1:ℝ)^(a+1) := by
  have hab : (-1:ℝ)^(b+1) = (-1:ℝ)^(a+1) := by
    rcases Nat.even_or_odd a with ha|ha
    · have hb : Even b := by rw [Nat.even_iff] at ha ⊢; omega
      rw [sign_even a ha, sign_even b hb]
    · have hb : Odd b := by rw [Nat.odd_iff] at ha ⊢; omega
      rw [sign_odd a ha, sign_odd b hb]
  linarith

theorem sign_add_ne (a b : ℕ) (h : a % 2 ≠ b % 2) :
    (-1:ℝ)^(a+1) + (-1:ℝ)^(b+1) = 0 := by
  rcases Nat.even_or_odd a with ha|ha
  · have hb : Odd b := by
      by_contra hcon
      have he : Even b := Nat.not_odd_iff_even.mp hcon
      rw [Nat.even_iff] at ha he
      exact h (by omega)
    rw [sign_even a ha, sign_odd b hb]; norm_num
  · have hb : Even b := by
      by_contra hcon
      have ho : Odd b := Nat.not_even_iff_odd.mp hcon
      rw [Nat.odd_iff] at ha ho
      exact h (by omega)
    rw [sign_odd a ha, sign_even b hb]; norm_num

end
end Entry13Ramanujanfactorial
end Ramanujan.Part1Ch6
