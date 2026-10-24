/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/MorgadoRegularResidues.lean -/

import Mathlib.Data.Nat.Totient
import sympy.atlas.NumberTheory.UnitaryDivisor
import Lemma.Set.UnitaryDivisor
import Mathlib.FieldTheory.Finite.Basic

open scoped BigOperators

namespace MetaMathlibExt

/-- The gcd fiber over a unitary divisor, as an equiv with coprime residues. -/
private def fiberEquiv (n : ℕ) (hn : 0 < n) (b : ℕ)
    (hb : b ∈ n.unitaryDivisors) :
    {m : ZMod n // m.val.gcd n = b}
      ≃ {k : ZMod (n / b) // k.val.Coprime (n / b)} := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hbdvd : b ∣ n := Nat.dvd_of_mem_unitaryDivisors hb
  have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hbdvd hn
  have hvpos : 0 < n / b := Nat.div_pos (Nat.le_of_dvd hn hbdvd) hbpos
  haveI : NeZero (n / b) := ⟨ne_of_gt hvpos⟩
  have hn_eq : b * (n / b) = n := Nat.mul_div_cancel' hbdvd
  have hcast_n : ∀ a : ZMod n, ((a.val : ℕ) : ZMod n) = a := fun a => by simp
  have hcast_v : ∀ k : ZMod (n / b), ((k.val : ℕ) : ZMod (n / b)) = k :=
    fun k => by simp
  refine ⟨fun av => ?_, fun kv => ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := av
    refine ⟨((a.val / b : ℕ) : ZMod (n / b)), ?_⟩
    have hlt : a.val / b < n / b := by
      rw [Nat.div_lt_iff_lt_mul hbpos]
      calc a.val < n := ZMod.val_lt a
        _ = b * (n / b) := hn_eq.symm
        _ = n / b * b := mul_comm _ _
    rw [ZMod.val_natCast_of_lt hlt]
    have h0 : 0 < a.val.gcd n := ha.symm ▸ hbpos
    have hcop := Nat.coprime_div_gcd_div_gcd h0
    rwa [ha] at hcop
  · obtain ⟨k, hk⟩ := kv
    refine ⟨((b * k.val : ℕ) : ZMod n), ?_⟩
    have hlt : b * k.val < n := by
      have hvk := ZMod.val_lt k
      have hmul := Nat.mul_lt_mul_of_pos_left hvk hbpos
      rwa [hn_eq] at hmul
    have e1 : (b * k.val).gcd (b * (n / b)) = (b * k.val).gcd n :=
      congrArg _ hn_eq
    rw [ZMod.val_natCast_of_lt hlt, ← e1, Nat.gcd_mul_left,
      hk.gcd_eq_one, mul_one]
  · intro xv
    obtain ⟨a, ha⟩ := xv
    apply Subtype.ext
    change ((b * ((((a.val / b : ℕ)) : ZMod (n / b)).val) : ℕ) : ZMod n) = a
    have hlt : a.val / b < n / b := by
      rw [Nat.div_lt_iff_lt_mul hbpos]
      calc a.val < n := ZMod.val_lt a
        _ = b * (n / b) := hn_eq.symm
        _ = n / b * b := mul_comm _ _
    have hdvd : b ∣ a.val := ha ▸ Nat.gcd_dvd_left _ _
    have hmul : b * (a.val / b) = a.val := Nat.mul_div_cancel' hdvd
    rw [ZMod.val_natCast_of_lt hlt, hmul]
    exact hcast_n a
  · intro xv
    obtain ⟨k, hk⟩ := xv
    apply Subtype.ext
    change (((((b * k.val : ℕ) : ZMod n).val / b : ℕ)) : ZMod (n / b)) = k
    have hlt : b * k.val < n := by
      have hvk := ZMod.val_lt k
      have hmul := Nat.mul_lt_mul_of_pos_left hvk hbpos
      rwa [hn_eq] at hmul
    rw [ZMod.val_natCast_of_lt hlt, Nat.mul_div_cancel_left _ hbpos]
    exact hcast_v k
end MetaMathlibExt
