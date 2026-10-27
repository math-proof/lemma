import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[IsLocalRing_isAlgClosed_residueField_and_charP_and_isUnit_and_ker_mul_ker_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_isAlgClosed_residueField_and_charP_and_isUnit_and_ker_mul_ker_of_surjective.lean)
-/
@[path]
private lemma main
  {B : Type u} [CommRing B] [IsLocalRing B]
  {B' : Type u} [CommRing B'] [IsLocalRing B']
  (σ : RingHom B' B)
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p] [IsAlgClosed (ResidueField B)]
  (q q' : ℕ) [Fact q.Prime] [Fact q'.Prime]
  -- given
  (hσ : Function.Surjective σ)
  (hsmall : RingHom.ker σ * maximalIdeal B' = ⊥)
  (hpq : p ≠ q)
  (hpq' : p ≠ q') :
  -- imply
  IsAlgClosed (ResidueField B') ∧ CharP (ResidueField B') p ∧
    IsUnit ((q * q' : ℕ) : B') ∧ RingHom.ker σ * RingHom.ker σ = ⊥ := by
  -- proof
  let _ : IsLocalHom σ := IsLocalHom.of_surjective σ hσ
  let ρ : RingHom (ResidueField B') (ResidueField B) := ResidueField.map σ
  have hρsurj : Function.Surjective ρ := by
    intro y
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨b', rfl⟩ := hσ b
    refine ⟨residue B' b', rfl⟩
  have hρbij : Function.Bijective ρ := ⟨ρ.injective, hρsurj⟩
  let e : ResidueField B' ≃+* ResidueField B := RingEquiv.ofBijective ρ hρbij
  have hchar : CharP (ResidueField B') p := (RingHom.charP_iff_charP ρ p).mpr inferInstance
  refine ⟨IsAlgClosed.of_ringEquiv (ResidueField B) (ResidueField B') e.symm, hchar, ?_, ?_⟩
  ·
    let _ := hchar
    rw [← residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_mul]
    apply mul_ne_zero
    ·
      rw [Ne, CharP.cast_eq_zero_iff (ResidueField B') p q]
      intro h
      apply hpq ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h)
    ·
      rw [Ne, CharP.cast_eq_zero_iff (ResidueField B') p q']
      intro h
      apply hpq' ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h)
  ·
    have hle : RingHom.ker σ ≤ maximalIdeal B' := le_maximalIdeal (RingHom.ker_ne_top σ)
    refine le_bot_iff.mp ?_
    calc
      _ ≤ RingHom.ker σ * maximalIdeal B' := Ideal.mul_mono_right hle
      _ = ⊥ := hsmall


-- created on 2026-10-20
