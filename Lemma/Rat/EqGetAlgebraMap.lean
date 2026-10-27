import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IsDiscreteValuationRing_exists_ringHom_padicInt_of_isFractionRing_rat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDiscreteValuationRing_exists_ringHom_padicInt_of_isFractionRing_rat.lean)
-/
@[path]
private lemma main
  (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R ℚ] [IsFractionRing R ℚ]
  (p : ℕ) [Fact p.Prime]
  -- given
  (hp : Irreducible (p : R)) :
  -- imply
  ∃ f : RingHom R ℤ_[p], ∀ r : R, ((f r : ℤ_[p]) : ℚ_[p]) = (algebraMap ℚ ℚ_[p]) (algebraMap R ℚ r) := by
  -- proof
  have hden : ∀ r : R, ¬ (p : ℕ) ∣ (algebraMap R ℚ r).den := by
    intro r hdvd
    set q := algebraMap R ℚ r with hq
    have hinj : Function.Injective (algebraMap R ℚ) := IsFractionRing.injective R ℚ
    have hrel : (q.den : R) * r = (q.num : R) := by
      apply hinj
      rw [map_mul, map_natCast, map_intCast, ← hq, mul_comm]
      exact_mod_cast Rat.mul_den_eq_num q
    have hdenp : (p : R) ∣ (q.den : R) := Nat.cast_dvd_cast hdvd
    have hnump : (p : R) ∣ (q.num : R) := hrel ▸ hdenp.mul_right r
    obtain ⟨a, b, hab⟩ : IsCoprime (q.num : ℤ) (q.den : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact_mod_cast q.reduced
    have h1 : (a : R) * (q.num : R) + (b : R) * (q.den : R) = 1 := by
      have := congrArg (Int.castRingHom R) hab
      simpa using this
    refine hp.not_isUnit (isUnit_of_dvd_one (h1 ▸ dvd_add (hnump.mul_left a) (hdenp.mul_left b)))
  have hnorm : ∀ r : R, ‖((algebraMap R ℚ r : ℚ) : ℚ_[p])‖ ≤ 1 := fun r => Padic.norm_rat_le_one (hden r)
  have halg : ∀ q : ℚ, (algebraMap ℚ ℚ_[p]) q = (q : ℚ_[p]) := fun q => eq_ratCast (algebraMap ℚ ℚ_[p]) q
  refine Exists.intro ({
    toFun := fun r => Subtype.mk ((algebraMap ℚ ℚ_[p]) (algebraMap R ℚ r)) (halg _ ▸ hnorm r)
    map_one' := PadicInt.ext (by simp)
    map_mul' := fun x y => PadicInt.ext (by simp)
    map_zero' := PadicInt.ext (by simp)
    map_add' := fun x y => PadicInt.ext (by simp) } : RingHom R ℤ_[p]) (fun r => rfl)


-- created on 2026-10-20
