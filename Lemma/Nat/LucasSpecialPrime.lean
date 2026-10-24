import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LucasSpecialPrime
open MetaMathlibExt


namespace MetaMathlibExt

/--
[isLucasSpecialPrime_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasSpecialPrime.lean)
-/
@[path]
lemma isLucasSpecialPrime_iff
  {P Q : Int}
  {p : Nat} :
-- imply
  IsLucasSpecialPrime P Q p ↔ Nat.Prime p ∧ (p : Int) ∣ P ∧ (p : Int) ∣ Q := by
-- proof
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


-- created on 2026-10-20
-- updated on 2026-10-23
