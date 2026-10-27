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
import Def.Analysis.SpecialFunctions.Part1Ch6Entry13Ramanujanfactorial
/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 13

Two series in powers of x are summable and equal for |x|>1.
-/


namespace Ramanujan.Part1Ch6

namespace Entry13Ramanujanfactorial

open scoped Nat Real BigOperators Interval Polynomial

open Asymptotics Filter Finset Complex Topology

noncomputable section

theorem dblL_summable {t : ℝ} (ht : ‖t‖ < 1) : Summable (dblL t) := by
  apply Summable.of_norm
  have hU := (summable_prod_mul_pow (𝕜 := ℝ) 0 ht).norm
  refine hU.congr (fun c => ?_)
  simp only [dblL, signW]
  have h1 : ‖(((c.2 : ℕ+) : ℕ) : ℝ) ^ (0:ℕ)‖ = 1 := by simp
  have hs : ‖(-1 : ℝ) ^ ((c.1 : ℕ) + 1)‖ = 1 := by simp
  rw [norm_mul, norm_mul, h1, hs, one_mul]

theorem tsum_pnat_pow (u : ℝ) (hu : ‖u‖ < 1) :
    ∑' m : ℕ+, u ^ ((m : ℕ)) = u / (1 - u) := by
  have hgeo := tsum_geometric_of_norm_lt_one (K := ℝ) (ξ := u) hu
  have h2 : ∑' m : ℕ+, u ^ ((m : ℕ)) = ∑' n : ℕ, u ^ (n + 1) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n => u ^ n)]
  rw [h2]
  simp only [pow_succ']
  rw [tsum_mul_left, hgeo, div_eq_mul_inv]

theorem inner_eq {t : ℝ} (ht : ‖t‖ < 1) (k : ℕ+) :
    ∑' m : ℕ+, dblL t (k, m) = signW k * (t ^ (k:ℕ) / (1 - t ^ (k:ℕ))) := by
  have hk : (k:ℕ) ≠ 0 := ne_of_gt k.2
  have htk : ‖t ^ (k:ℕ)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) ht hk
  simp only [dblL]
  have hexp : ∀ m : ℕ+, t ^ ((k:ℕ) * (m:ℕ)) = (t ^ (k:ℕ)) ^ ((m:ℕ)) := by
    intro m; rw [pow_mul]
  simp only [hexp]
  rw [tsum_mul_left]
  congr 1
  exact tsum_pnat_pow _ htk

theorem finite_left (N : ℕ) (t : ℝ) :
    ∑ x ∈ N.divisorsAntidiagonal, ((-1:ℝ)^(x.1+1) * t^(x.1*x.2))
      = (∑ d ∈ N.divisors, (-1:ℝ)^(d+1)) * t^N := by
  have h1 : ∑ x ∈ N.divisorsAntidiagonal, ((-1:ℝ)^(x.1+1) * t^(x.1*x.2))
      = ∑ x ∈ N.divisorsAntidiagonal, ((-1:ℝ)^(x.1+1) * t^N) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hmem := Nat.mem_divisorsAntidiagonal.mp hx
    rw [hmem.1]
  rw [h1, ← Finset.sum_mul]
  congr 1
  have h2 := Nat.sum_divisorsAntidiagonal (M := ℝ) (f := fun a b => (-1:ℝ)^(a+1)) (n := N)
  simpa using h2

theorem left_tsum_eq {t : ℝ} (ht : ‖t‖ < 1) :
    ∑' c : ℕ+ × ℕ+, dblL t c
      = ∑' N : ℕ+, (∑ d ∈ (N:ℕ).divisors, (-1:ℝ)^(d+1)) * t^((N:ℕ)) := by
  have hsum : Summable (dblL t) := dblL_summable ht
  have hsig : Summable (fun c : (N : ℕ+) × ↥((N:ℕ).divisorsAntidiagonal) ↦
      dblL t (sigmaAntidiagonalEquivProd c)) :=
    sigmaAntidiagonalEquivProd.summable_iff.mpr hsum
  rw [← sigmaAntidiagonalEquivProd.tsum_eq]
  rw [Summable.tsum_sigma hsig]
  refine tsum_congr fun N => ?_
  have hgx : ∀ x : ↥((N:ℕ).divisorsAntidiagonal),
      dblL t (sigmaAntidiagonalEquivProd ⟨N, x⟩)
        = ((-1:ℝ)^(x.1.1+1) * t^(x.1.1*x.1.2)) := by
    intro x
    simp only [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, dblL, signW,
      Equiv.coe_fn_mk, PNat.mk_coe]
  rw [tsum_fintype]
  have hstep : ∑ x : ↥((N:ℕ).divisorsAntidiagonal),
        dblL t (sigmaAntidiagonalEquivProd ⟨N, x⟩)
      = ∑ x ∈ (N:ℕ).divisorsAntidiagonal, ((-1:ℝ)^(x.1+1) * t^(x.1*x.2)) := by
    rw [← Finset.sum_attach ((N:ℕ).divisorsAntidiagonal)
      (fun p : ℕ × ℕ => (-1:ℝ)^(p.1+1) * t^(p.1*p.2))]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hgx]
  rw [hstep]
  exact finite_left (N:ℕ) t

theorem left_single_eq {t : ℝ} (ht : ‖t‖ < 1) :
    ∑' k : ℕ+, signW k * (t ^ (k:ℕ) / (1 - t ^ (k:ℕ)))
      = ∑' N : ℕ+, (∑ d ∈ (N:ℕ).divisors, (-1:ℝ)^(d+1)) * t^((N:ℕ)) := by
  have hsum := dblL_summable ht
  have e1 : (∑' k : ℕ+, signW k * (t ^ (k:ℕ) / (1 - t ^ (k:ℕ))))
      = ∑' k : ℕ+, ∑' m : ℕ+, dblL t (k, m) := by
    refine tsum_congr fun k => ?_
    rw [inner_eq ht k]
  rw [e1, ← hsum.tsum_prod]
  exact left_tsum_eq ht

end
end Entry13Ramanujanfactorial
end Ramanujan.Part1Ch6
