import Mathlib
import sympy.Basic


/--
[PadicInt_nonempty_ringHom_of_isAdicComplete_of_natCast_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PadicInt_nonempty_ringHom_of_isAdicComplete_of_natCast_mem.lean)
-/
@[main]
private lemma main
  [CommRing S]
  {I : Ideal S} [IsAdicComplete I S]
  {p : ℕ} [Fact p.Prime]
-- given
  (hp : (p : S) ∈ I) :
-- imply
  Nonempty (ℤ_[p] →+* S) := by
-- proof
  classical

  let g : (n : ℕ) → ZMod (p ^ n) →+* S ⧸ I ^ n := fun n =>
    (Ideal.Quotient.lift (Ideal.span {((p ^ n : ℕ) : ℤ)})
      ((Ideal.Quotient.mk (I ^ n)).comp (Int.castRingHom S)) (by
        have h0 : (Ideal.Quotient.mk (I ^ n)) ((Int.castRingHom S) ((p ^ n : ℕ) : ℤ)) = 0 := by
          rw [eq_intCast, Int.cast_natCast, Nat.cast_pow, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.pow_mem_pow hp n
        intro a ha
        rw [Ideal.mem_span_singleton] at ha
        obtain ⟨b, rfl⟩ := ha
        simp only [RingHom.comp_apply, map_mul, h0, zero_mul])).comp
    (Int.quotientSpanNatEquivZMod (p ^ n)).symm.toRingHom
  let f : (n : ℕ) → ℤ_[p] →+* S ⧸ I ^ n := fun n => (g n).comp (PadicInt.toZModPow n)
  refine ⟨IsAdicComplete.liftRingHom I f ?_⟩
  intro m n hle
  show ((Ideal.Quotient.factorPow I hle).comp (g n)).comp (PadicInt.toZModPow n)
    = (g m).comp (PadicInt.toZModPow m)
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle]
  exact congrArg (fun φ : ZMod (p ^ n) →+* S ⧸ I ^ m => φ.comp (PadicInt.toZModPow n))
    (RingHom.ext_zmod ((Ideal.Quotient.factorPow I hle).comp (g n))
      ((g m).comp (ZMod.castHom (pow_dvd_pow p hle) (ZMod (p ^ m)))))


-- created on 2026-10-05
