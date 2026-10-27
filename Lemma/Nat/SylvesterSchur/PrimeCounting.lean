import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped BigOperators
open Finset Nat


namespace Nat.SylvesterSchur

/--
[exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/PrimeCounting.lean)
-/
@[path]
lemma exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le
  {N r : ℕ}
-- given
  (hsmall : ¬ ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
-- imply
  ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
-- proof
  by_contra h
  exact hsmall fun p hp hdvd => le_of_not_gt fun hgt => h ⟨p, hp, hgt, hdvd⟩

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[exists_large_prime_dvd_choose_of_upper_lt_lower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/PrimeCounting.lean)
-/
@[path]
lemma exists_large_prime_dvd_choose_of_upper_lt_lower
  {N r U : ℕ}
-- given
  (hupper : (∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) → Nat.choose N r ≤ U)
  (hbound : (U : ℚ) < ((N + 1 - r : ℕ) ^ r : ℚ) / (r ! : ℚ)) :
-- imply
  ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
-- proof
  apply exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le
  intro hsmall
  have hupper_q : ((Nat.choose N r : ℕ) : ℚ) ≤ (U : ℚ) := by
    exact_mod_cast hupper hsmall
  have hlower :
    ((N + 1 - r : ℕ) ^ r : ℚ) / (r ! : ℚ) ≤ ((Nat.choose N r : ℕ) : ℚ) :=
    Nat.pow_le_choose (α := ℚ) r N
  exact (not_lt_of_ge (hlower.trans hupper_q)) hbound

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[primeCounting_le_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/PrimeCounting.lean)
-/
@[path]
lemma primeCounting_le_sub_one
  {r : ℕ}
-- given
  (hr : 2 ≤ r) :
-- imply
  Nat.primeCounting r ≤ r - 1 := by
-- proof
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting' (r + 1)]
  have hsubset :
    (r + 1).primesBelow ⊆ Finset.Icc 2 r := by
    intro p hp
    rw [Finset.mem_Icc]
    exact ⟨(Nat.prime_of_mem_primesBelow hp).two_le, by
      have hlt := Nat.lt_of_mem_primesBelow hp
      omega⟩
  exact (Finset.card_le_card hsubset).trans_eq (by rw [card_Icc]; omega)

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[primeCounting_le_half_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/PrimeCounting.lean)
-/
@[path]
lemma primeCounting_le_half_add_one
  {r : ℕ} :
-- imply
  Nat.primeCounting r ≤ r / 2 + 1 := by
-- proof
  by_cases hr : r ≤ 1
  · have hz : Nat.primeCounting r = 0 := Nat.primeCounting_eq_zero_iff.mpr hr
    omega
  · have hr2 : 2 ≤ r := by omega
    have h :=
      Nat.primeCounting'_add_le (a := 2) (k := 3) (by decide) (by decide) (r - 2)
    have harg : 3 + (r - 2) = r + 1 := by omega
    have hpi3 : Nat.primeCounting' 3 = 1 := by decide
    have htot : Nat.totient 2 = 1 := by decide
    rw [harg, hpi3, htot, one_mul] at h
    change Nat.primeCounting' (r + 1) ≤ r / 2 + 1
    omega

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[primeCounting_le_mod_thirty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/PrimeCounting.lean)
-/
@[path]
`31`, every prime is coprime to `30`, and Mathlib's `Nat.primeCounting'_add_le` counts at most
one residue-class block plus a tail. -/
private lemma primeCounting_le_mod_thirty (r : ℕ) :
  Nat.primeCounting r ≤ 10 + 8 * ((r - 30) / 30 + 1) := by
  by_cases hr : r ≤ 30
  · have hmono : Nat.primeCounting r ≤ Nat.primeCounting 30 :=
    Nat.monotone_primeCounting hr
    have hpi30 : Nat.primeCounting 30 = 10 := by decide
    omega
  · have h :=
    Nat.primeCounting'_add_le (a := 30) (k := 31) (by decide) (by decide) (r - 30)
    have harg : 31 + (r - 30) = r + 1 := by omega
    have hpi31 : Nat.primeCounting' 31 = 10 := by decide
    have htot : Nat.totient 30 = 8 := by decide
    rw [harg, hpi31, htot] at h
    change Nat.primeCounting' (r + 1) ≤ 10 + 8 * ((r - 30) / 30 + 1)
    exact h

end Nat.SylvesterSchur

namespace Nat.SylvesterSchur

/--
[primeCounting_le_three_mul_div_eight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/PrimeCounting.lean)
-/
@[path]
lemma primeCounting_le_three_mul_div_eight
  {r : ℕ}
-- given
  (hr : 38 ≤ r) :
-- imply
  Nat.primeCounting r ≤ 3 * r / 8 := by
-- proof
  by_cases h91 : 91 ≤ r
  · exact (primeCounting_le_mod_thirty r).trans (by omega)
  · interval_cases r <;> decide

end Nat.SylvesterSchur


-- created on 2026-10-20
-- updated on 2026-10-26
