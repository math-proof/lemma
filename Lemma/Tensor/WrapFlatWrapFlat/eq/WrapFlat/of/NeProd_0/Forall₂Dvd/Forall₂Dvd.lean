import sympy.core.mul
import sympy.Basic
import Lemma.Tensor.WrapFlat.eq.WrapFlatMod.of.EqLengthS
open Tensor


@[path]
private lemma main
-- given
  (s mid out : List ℕ)
  (i : ℕ)
  (hsm : List.Forall₂ (fun a b => a ∣ b) s mid)
  (hmo : List.Forall₂ (fun a b => a ∣ b) mid out)
  (hmid : mid.prod ≠ 0) :
-- imply
  wrapFlat s mid (wrapFlat mid out i) = wrapFlat s out i := by
-- proof
  induction hsm generalizing out i with
  | nil =>
    cases hmo
    simp [wrapFlat]
  | @cons n m s mid hnm _ ih =>
    cases hmo with
    | @cons _ k _ tout hmk hmo =>
      have hm : m ≠ 0 := by
        intro hz
        simp [hz] at hmid
      have hmt : mid.prod ≠ 0 := by
        intro hz
        simp [hz] at hmid
      simp only [wrapFlat]
      have hr : wrapFlat mid tout i < mid.prod :=
        wrapFlat_lt mid tout (List.Forall₂.length_eq hmo) hmt i
      have hdiv :
          ((i / tout.prod % k % m) * mid.prod + wrapFlat mid tout i) / mid.prod =
            i / tout.prod % k % m := by
        rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero hmt),
          Nat.div_eq_of_lt hr, zero_add]
      have hmod' :
          ((i / tout.prod % k % m) * mid.prod + wrapFlat mid tout i) % mid.prod =
            wrapFlat mid tout i := by
        rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
      rw [hdiv, Nat.mod_mod, Nat.mod_mod_of_dvd (i / tout.prod % k) hnm]
      have hlen_sm : s.length = mid.length := List.Forall₂.length_eq ‹_›
      rw [WrapFlat.eq.WrapFlatMod.of.EqLengthS s mid hlen_sm, hmod', ih tout i hmo hmt]


-- created on 2026-10-07
