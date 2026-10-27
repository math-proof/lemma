import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.EllipticCurves.code.FrobeniusEndomorphism.Part2
import Lemma.Complex.Atlas.v1.EllipticCurves.code.FrobeniusEndomorphism
import Lemma.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part3


namespace Schoof

/--
[addOrderOf_eq_prime_of_torsion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Schoof.lean)
-/
@[path]
lemma addOrderOf_eq_prime_of_torsion
  {F : Type u}
  [Field F]
  [DecidableEq F]
  [AddGroup G]
  {P : G}
  {ℓ : ℕ}
-- given
  (hℓ : Nat.Prime ℓ)
  (hP : (ℓ : ℤ) • P = 0)
  (hne : P ≠ 0) :
-- imply
  addOrderOf P = ℓ := by
-- proof
  have h1 : addOrderOf P ∣ ℓ := by
    have := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hP
    exact_mod_cast this
  obtain h | h := hℓ.eq_one_or_self_of_dvd _ h1
  · exfalso; apply hne
    rw [← one_smul ℤ P, ← addOrderOf_nsmul_eq_zero P]
    simp [h]
  · exact h

end Schoof

namespace Schoof

/--
[zmod_eq_of_dvd_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Schoof.lean)
-/
@[path]
lemma zmod_eq_of_dvd_sub
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {c t : ℤ}
  {ℓ : ℕ}
-- given
  (hdvd : (ℓ : ℤ) ∣ (c - t)) :
-- imply
  (c : ZMod ℓ) = (t : ZMod ℓ) := by
-- proof
  have h : ((c - t : ℤ) : ZMod ℓ) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (c - t) ℓ).mpr hdvd
  simp only [Int.cast_sub] at h
  exact sub_eq_zero.mp h

end Schoof

namespace Schoof

/--
[frobenius_trace_mod_ell](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Schoof.lean)
-/
@[path]
lemma frobenius_trace_mod_ell
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
  {π : W.Point →+ W.Point}
  {t q : ℤ}
  {ℓ : ℕ}
  {P : W.Point}
  {c : ℤ}
-- given
  (hℓ : Nat.Prime ℓ)
  (char_eq : ∀ P : W.Point, (ℓ : ℤ) • P = 0 → π (π P) - t • (π P) + q • P = 0)
  (frob_torsion : ∀ P : W.Point, (ℓ : ℤ) • P = 0 → (ℓ : ℤ) • (π P) = 0)
  (frob_nonzero : ∀ P : W.Point, (ℓ : ℤ) • P = 0 → P ≠ 0 → π P ≠ 0)
  (hP_torsion : (ℓ : ℤ) • P = 0)
  (hP_ne : P ≠ 0)
  (hc : π (π P) - c • (π P) + q • P = 0) :
-- imply
  (c : ZMod ℓ) = (t : ZMod ℓ) := by
-- proof
  have hchar := char_eq P hP_torsion
  have h_c : π (π P) + q • P = c • (π P) := by
    rw [sub_add_eq_add_sub] at hc; exact sub_eq_zero.mp hc
  have h_t : π (π P) + q • P = t • (π P) := by
    rw [sub_add_eq_add_sub] at hchar; exact sub_eq_zero.mp hchar
  have h_eq : c • (π P) = t • (π P) := by rw [← h_c, h_t]
  have h_sub : (c - t) • (π P) = 0 := by rw [sub_smul, h_eq, sub_self]
  have hπP_ne := frob_nonzero P hP_torsion hP_ne
  have hπP_tor := frob_torsion P hP_torsion
  have hord := addOrderOf_eq_prime_of_torsion hℓ hπP_tor hπP_ne
  have hdvd : (ℓ : ℤ) ∣ (c - t) := by
    rw [← hord]; exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr h_sub
  exact zmod_eq_of_dvd_sub hdvd

end Schoof


-- created on 2026-10-23
