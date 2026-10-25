/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Multiset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Def.Combinatorics.Enumerative.Partition.Overpartition
import Lemma.Nat.Enumerative.Partition.Overpartition
import Lemma.Nat.QuadraticForms.ThreeSquares
import Lemma.Real.SpecialFunctions.JacobiTripleProduct
import Def.NumberTheory.QuadraticForms.ThreeSquares
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Def.Analysis.SpecialFunctions.JacobiTripleProduct
import Def.Combinatorics.Enumerative.Partition.OverpartitionCongruence.Part9


namespace MetaMathlibExt

/--
For every positive `n`, the number of overpartitions of `5n` is congruent modulo `5`
to `(-1)ⁿ` times the number of ordered representations of `n` as three integer squares.

Liuquan Wang, "Another Proof of a Conjecture by Hirschhorn and Sellers on Overpartitions,"
Journal of Integer Sequences 17 (2014), Article 14.9.8,
Theorem (label thm1), lines 110–114.
`https://cs.uwaterloo.ca/journals/JIS/VOL17/Wang2/wang15.tex`

Proves `Wanted` entry `overpartition_mul_five_mod_five`.
-/
theorem overpartition_mul_five_mod_five
    (n : ℕ) (hn : 1 ≤ n) :
    Int.ModEq 5
      (Nat.card {
        p : Multiset ℕ × Finset ℕ //
          (∀ a ∈ p.1, 0 < a) ∧
          p.1.sum = 5 * n ∧
          ∀ a ∈ p.2, a ∈ p.1
      })
      (((-1 : ℤ) ^ n) * Nat.card {
        x : ℤ × ℤ × ℤ //
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = n
      }) := by
  obtain ⟨W, R₁, R₂, R₃, R₄, hR1, hR2, hR3, hR4, hdecomp⟩ :=
    opc_theta_pow_four_decomp
  have hfact : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmap8 : opcPhi5 * opcQ5 = 1 := by
    have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 5)))
      opc_theta_mul_rescale_genFun
    rwa [map_mul, map_one] at h
  have hFrob : PowerSeries.expand 5 opc_five_ne_zero opcQ5 = opcQ5 ^ 5 := by
    have h0 : ((PowerSeries.expand 5 opc_five_ne_zero opcQ5).map
        (frobenius (ZMod 5) 5)) = opcQ5 ^ 5 :=
      PowerSeries.map_frobenius_expand 5 opc_five_ne_zero
    rw [ZMod.frobenius_zmod 5, PowerSeries.map_id] at h0
    exact h0
  have hQ : opcPhi5 ^ 4 * PowerSeries.expand 5 opc_five_ne_zero opcQ5
      = opcQ5 := by
    have h4 : opcPhi5 ^ 4 * opcQ5 ^ 5 = opcQ5 * (opcPhi5 * opcQ5) ^ 4 := by
      ring
    rw [hFrob, h4, hmap8, one_pow, mul_one]
  have hmap12 : opcPhi5 ^ 4
        = PowerSeries.expand 5 opc_five_ne_zero (opcPhi5 ^ 4)
          + (((PowerSeries.map (Int.castRingHom (ZMod 5)) R₁
            + PowerSeries.map (Int.castRingHom (ZMod 5)) R₂)
            + PowerSeries.map (Int.castRingHom (ZMod 5)) R₃)
            + PowerSeries.map (Int.castRingHom (ZMod 5)) R₄) := by
    have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 5))) hdecomp
    simp only [map_add, PowerSeries.map_expand, map_nsmul] at h
    rw [map_pow] at h
    have h5W : (5 : ℕ) • PowerSeries.map (Int.castRingHom (ZMod 5)) W
        = 0 := by
      have h5c : ∀ c : ZMod 5, (5 : ℕ) • c = 0 := by
        intro c
        rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      apply PowerSeries.ext
      intro k
      rw [map_nsmul]
      exact h5c _
    rw [h5W, add_zero] at h
    exact h
  have hz : ∀ (S : PowerSeries (ZMod 5)) (k : ZMod 5),
      opcSupportedMod (ZMod 5) 5 k S → k ≠ 0 →
        PowerSeries.coeff (5 * n)
          (S * PowerSeries.expand 5 opc_five_ne_zero opcQ5) = 0 := by
    intro S k hS hk
    have hE : opcSupportedMod (ZMod 5) 5 0
        (PowerSeries.expand 5 opc_five_ne_zero opcQ5) :=
      opc_supportedMod_expand 5 opc_five_ne_zero opcQ5
    have hP := opc_supportedMod_mul 5 k 0 _ _ hS hE
    have hk0 : k + 0 ≠ 0 := by simpa using hk
    have hNe : NeZero 5 := ⟨opc_five_ne_zero⟩
    exact opc_supportedMod_coeff_eq_zero 5 (k + 0) _ hP hk0 n
  have hk1 : (1 : ZMod 5) ≠ 0 := by
    intro h
    have h1 : (((1 : ℕ)) : ZMod 5) = 0 := by
      rw [Nat.cast_one]
      exact h
    exact absurd ((ZMod.natCast_eq_zero_iff 1 5).mp h1) (by omega)
  have hk2 : (2 : ZMod 5) ≠ 0 := by
    intro h
    have h2 : (((2 : ℕ)) : ZMod 5) = 0 := by simpa using h
    exact absurd ((ZMod.natCast_eq_zero_iff 2 5).mp h2) (by omega)
  have hk3 : (3 : ZMod 5) ≠ 0 := by
    intro h
    have h3 : (((3 : ℕ)) : ZMod 5) = 0 := by simpa using h
    exact absurd ((ZMod.natCast_eq_zero_iff 3 5).mp h3) (by omega)
  have hk4 : (4 : ZMod 5) ≠ 0 := by
    intro h
    have h4 : (((4 : ℕ)) : ZMod 5) = 0 := by simpa using h
    exact absurd ((ZMod.natCast_eq_zero_iff 4 5).mp h4) (by omega)
  have hz1 := hz _ (1 : ZMod 5)
    (opc_supportedMod_map (Int.castRingHom (ZMod 5)) 5 1 _ hR1) hk1
  have hz2 := hz _ (2 : ZMod 5)
    (opc_supportedMod_map (Int.castRingHom (ZMod 5)) 5 2 _ hR2) hk2
  have hz3 := hz _ (3 : ZMod 5)
    (opc_supportedMod_map (Int.castRingHom (ZMod 5)) 5 3 _ hR3) hk3
  have hz4 := hz _ (4 : ZMod 5)
    (opc_supportedMod_map (Int.castRingHom (ZMod 5)) 5 4 _ hR4) hk4
  have h43 : opcPhi5 ^ 4 * opcQ5 = opcPhi5 ^ 3 := by
    have e : opcPhi5 ^ 4 * opcQ5 = opcPhi5 ^ 3 * (opcPhi5 * opcQ5) := by
      ring
    rw [e, hmap8, mul_one]
  have e3 : PowerSeries.expand 5 opc_five_ne_zero (opcPhi5 ^ 4)
        * PowerSeries.expand 5 opc_five_ne_zero opcQ5
        = PowerSeries.expand 5 opc_five_ne_zero (opcPhi5 ^ 3) := by
    rw [← map_mul, h43]
  have hQeq : opcQ5 = PowerSeries.expand 5 opc_five_ne_zero (opcPhi5 ^ 3)
      + (((PowerSeries.map (Int.castRingHom (ZMod 5)) R₁
        * PowerSeries.expand 5 opc_five_ne_zero opcQ5
        + PowerSeries.map (Int.castRingHom (ZMod 5)) R₂
        * PowerSeries.expand 5 opc_five_ne_zero opcQ5)
        + PowerSeries.map (Int.castRingHom (ZMod 5)) R₃
        * PowerSeries.expand 5 opc_five_ne_zero opcQ5)
        + PowerSeries.map (Int.castRingHom (ZMod 5)) R₄
        * PowerSeries.expand 5 opc_five_ne_zero opcQ5) := by
    conv_lhs => rw [← hQ, hmap12]
    linear_combination e3
  have hcoeff : PowerSeries.coeff (5 * n) opcQ5
      = PowerSeries.coeff n (opcPhi5 ^ 3) := by
    rw [hQeq, map_add, map_add, map_add, map_add, hz1, hz2, hz3, hz4,
      PowerSeries.coeff_expand_mul]
    simp
  have hsign : (-1 : ZMod 5) ^ (5 * n) = (-1) ^ n := by
    rw [pow_mul, show ((-1 : ZMod 5) ^ 5) = -1 from Odd.neg_one_pow ⟨2, rfl⟩]
  have hLHS : PowerSeries.coeff (5 * n) opcQ5
      = (-1 : ZMod 5) ^ n
        * (Int.castRingHom (ZMod 5)) (PowerSeries.coeff (5 * n)
          (Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ)))) := by
    unfold opcQ5
    rw [PowerSeries.coeff_map, PowerSeries.coeff_rescale, map_mul, map_pow,
      map_neg, map_one, hsign]
  have hRHS : PowerSeries.coeff n (opcPhi5 ^ 3)
      = (Int.castRingHom (ZMod 5)) (PowerSeries.coeff n (opcTheta ^ 3)) := by
    unfold opcPhi5
    rw [← map_pow, PowerSeries.coeff_map]
  have hN1 := opc_overpartition_card_eq_coeff_genFun (5 * n)
  have hN3 := opc_coeff_theta_cube n
  rw [← hN1] at hLHS
  rw [hN3] at hRHS
  -- hLHS : coeff-Q = (-1)^n * π ↑(card (opcOver (5n)))
  -- hRHS : coeff-Φ³ = π ↑(card three-sq)
  have hcomb : (-1 : ZMod 5) ^ n
        * (Int.castRingHom (ZMod 5))
          ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ)
      = (Int.castRingHom (ZMod 5))
        ((Nat.card {x : ℤ × ℤ × ℤ //
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (n : ℤ)} : ℕ) : ℤ) := by
    rw [← hLHS, ← hRHS]
    exact hcoeff
  have h2n : (-1 : ZMod 5) ^ n * (-1) ^ n = 1 := by
    rw [← pow_add, show n + n = 2 * n from by ring, pow_mul,
      show ((-1 : ZMod 5) ^ 2) = 1 from Even.neg_one_pow ⟨1, rfl⟩, one_pow]
  have hmain : (Int.castRingHom (ZMod 5))
        ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ)
      = (-1 : ZMod 5) ^ n * (Int.castRingHom (ZMod 5))
        ((Nat.card {x : ℤ × ℤ × ℤ //
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (n : ℤ)} : ℕ) : ℤ) := by
    calc (Int.castRingHom (ZMod 5))
            ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ)
        = ((-1 : ZMod 5) ^ n * (-1) ^ n)
          * (Int.castRingHom (ZMod 5))
            ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ) := by
          rw [h2n, one_mul]
      _ = (-1 : ZMod 5) ^ n * (((-1 : ZMod 5) ^ n
          * (Int.castRingHom (ZMod 5))
            ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ))) := by
          rw [mul_assoc]
      _ = _ := by rw [← hcomb]
  have hOverEq : opcOver (5 * n) = { p : Multiset ℕ × Finset ℕ //
      (∀ a ∈ p.1, 0 < a) ∧ p.1.sum = 5 * n ∧ ∀ a ∈ p.2, a ∈ p.1 } := rfl
  have hcard : ((Nat.card { p : Multiset ℕ × Finset ℕ //
      (∀ a ∈ p.1, 0 < a) ∧ p.1.sum = 5 * n ∧ ∀ a ∈ p.2, a ∈ p.1 } : ℕ) : ℤ)
      = ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ) := by
    rw [← hOverEq]
  have eNeg : (-1 : ZMod 5) ^ n
      = (Int.castRingHom (ZMod 5)) (((-1 : ℤ) ^ n)) := by
    rw [map_pow, map_neg, map_one]
  have hfin : ((((Nat.card (opcOver (5 * n)) : ℕ)) : ZMod 5))
      = ((((-1 : ℤ) ^ n * ((Nat.card {x : ℤ × ℤ × ℤ //
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (n : ℤ)} : ℕ) : ℤ) : ℤ))
        : ZMod 5) := by
    have h := hmain
    rw [eNeg, ← map_mul] at h
    exact h
  rw [hcard]
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hfin

end MetaMathlibExt
