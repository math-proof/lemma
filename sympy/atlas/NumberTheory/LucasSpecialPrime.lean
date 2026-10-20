/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasSpecialPrime.lean -/

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Int.Basic

namespace MetaMathlibExt

/-- Special prime for integral Lucas parameters (concept `jis_term_9fa09acd972f484f5b457a48`):
  `IsLucasSpecialPrime P Q p` means `p` is prime and `p` divides `Int.gcd P Q`.
  Sources: `jis_source_eb765815f14b18e047ccd51b`, `jis_source_e9bb56af5eef26576559cf4c`,
  `jis_source_de2518f50026ac96429ae911`. -/
def IsLucasSpecialPrime (P Q : Int) (p : Nat) : Prop :=
  Nat.Prime p ∧ p ∣ Int.gcd P Q

/-- Equivalence for special primes (concept `jis_term_9fa09acd972f484f5b457a48`):
  `IsLucasSpecialPrime P Q p` holds iff `p` is prime and its integer cast divides
  both `P` and `Q`. Sources: `jis_source_eb765815f14b18e047ccd51b`,
  `jis_source_e9bb56af5eef26576559cf4c`, `jis_source_de2518f50026ac96429ae911`. -/
theorem isLucasSpecialPrime_iff (P Q : Int) (p : Nat) :
    IsLucasSpecialPrime P Q p ↔ Nat.Prime p ∧ (p : Int) ∣ P ∧ (p : Int) ∣ Q := by
  unfold IsLucasSpecialPrime
  constructor
  · rintro ⟨hp, hdvd⟩
    have hgcd : Int.gcd P Q = Nat.gcd P.natAbs Q.natAbs :=
      Int.gcd_eq_natAbs_gcd_natAbs P Q
    rw [hgcd] at hdvd
    refine ⟨hp, ?_, ?_⟩
    · rw [Int.natCast_dvd]
      exact dvd_trans hdvd (Nat.gcd_dvd_left _ _)
    · rw [Int.natCast_dvd]
      exact dvd_trans hdvd (Nat.gcd_dvd_right _ _)
  · rintro ⟨hp, hP, hQ⟩
    exact ⟨hp, Int.dvd_gcd hP hQ⟩

end MetaMathlibExt
