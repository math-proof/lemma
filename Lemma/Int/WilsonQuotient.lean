import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.WilsonQuotient
open Int


namespace Int

/--
[mul_wilsonQuotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WilsonQuotient.lean)
-/
@[path]
lemma mul_wilsonQuotient
  {p : ℕ}
-- given
  (hp : Nat.Prime p) :
-- imply
  (p : ℤ) * wilsonQuotient p = (Nat.factorial (p - 1) : ℤ) + 1 := by
-- proof
  unfold wilsonQuotient
  have h_dvd : (p : ℤ) ∣ ((Nat.factorial (p - 1) : ℤ) + 1) := by
    let _ := Fact.mk hp
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [ZMod.wilsons_lemma p]
    simp
  exact Int.mul_ediv_cancel' h_dvd

end Int

namespace Int

/--
[factorial_eq_mul_wilsonQuotient_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WilsonQuotient.lean)
-/
@[path]
lemma factorial_eq_mul_wilsonQuotient_sub_one
  {p : ℕ}
-- given
  (hp : Nat.Prime p) :
-- imply
  (Nat.factorial (p - 1) : ℤ) = (p : ℤ) * wilsonQuotient p - 1 := by
-- proof
  have h := mul_wilsonQuotient p hp
  omega

end Int


-- created on 2026-10-20
-- updated on 2026-10-23
