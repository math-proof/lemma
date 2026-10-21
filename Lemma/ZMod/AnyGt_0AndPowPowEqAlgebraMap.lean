import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[HopfAlgebra_exists_forall_pow_pow_eq_algebraMap_counit_of_isLocalRing_zmodp](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_exists_forall_pow_pow_eq_algebraMap_counit_of_isLocalRing_zmodp.lean)
-/
@[path]
private lemma main
  (p : ℕ) [Fact p.Prime]
  (B : Type) [CommRing B] [HopfAlgebra (ZMod p) B] [Module.Finite (ZMod p) B]
  (hB : IsLocalRing B) :
  -- imply
  ∃ N : ℕ, 0 < N ∧ ∀ x : B, x ^ p ^ N = algebraMap (ZMod p) B (Coalgebra.counit (R := ZMod p) x) := by
  -- proof
  classical
  let _ := hB
  let _ : Nontrivial B := (Bialgebra.counitAlgHom (ZMod p) B : RingHom B (ZMod p)).domain_nontrivial
  let _ : CharP B p := charP_of_injective_algebraMap (algebraMap (ZMod p) B).injective p
  let _ : IsArtinianRing B := isArtinian_of_tower (ZMod p) inferInstance
  have hJ : IsNilpotent (maximalIdeal B) := by
    rw [← jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    apply IsArtinianRing.isNilpotent_jacobson_bot
  obtain ⟨m, hm⟩ := hJ
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  refine ⟨m + 1, Nat.succ_pos m, fun x => ?_⟩
  have hle : m ≤ p ^ (m + 1) := calc
    _ ≤ 2 ^ m := Nat.le_of_lt Nat.lt_two_pow_self
    _ ≤ p ^ m := Nat.pow_le_pow_left hp2 m
    _ ≤ p ^ (m + 1) := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (Nat.le_succ m)
  have hzmod : ∀ (k : ℕ) (a : ZMod p), a ^ p ^ k = a := by
    intro k
    induction k with
    | zero =>
      intro a
      simp
    | succ k ih =>
      intro a
      rw [pow_succ, pow_mul, ih, ZMod.pow_card]
  set c := algebraMap (ZMod p) B (Coalgebra.counit (R := ZMod p) x) with hc
  set n := x - c with hn
  have hnm : n ∈ maximalIdeal B := by
    have hker : n ∈ RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B) := by
      rw [RingHom.mem_ker, hn, map_sub]
      change Coalgebra.counit (R := ZMod p) x - Bialgebra.counitAlgHom (ZMod p) B (algebraMap (ZMod p) B (Coalgebra.counit (R := ZMod p) x)) = 0
      rw [AlgHom.commutes]
      apply sub_self _
    refine le_maximalIdeal (RingHom.ker_ne_top _) hker
  have hn0 : n ^ p ^ (m + 1) = 0 := by
    have hnm' : n ^ m = 0 := by
      have hpow : n ^ m ∈ (maximalIdeal B) ^ m := Ideal.pow_mem_pow hnm m
      rw [hm] at hpow
      apply Ideal.mem_bot.mp hpow
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    rw [hd, pow_add, hnm', zero_mul]
  have hcq : c ^ p ^ (m + 1) = c := by
    rw [hc, ← map_pow, hzmod]
  calc
    _ = (c + n) ^ p ^ (m + 1) := by
      rw [hn, add_sub_cancel]
    _ = c ^ p ^ (m + 1) + n ^ p ^ (m + 1) := add_pow_char_pow c n p (m + 1)
    _ = c := by
      rw [hcq, hn0, add_zero]


-- created on 2026-10-20
