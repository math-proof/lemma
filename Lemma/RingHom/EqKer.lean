import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Ideal_exists_ringHom_integralClosure_ker_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_exists_ringHom_integralClosure_ker_eq.lean)
-/
@[path]
private lemma main
  {T : Type u} [CommRing T] [Module.Finite ℤ T]
  (𝔓 : Ideal T) (h𝔓 : 𝔓.IsPrime)
  (hint : ∀ n : ℤ, (n : T) ∈ 𝔓 → n = 0) :
  -- imply
  ∃ f : RingHom T (integralClosure ℤ ℂ), RingHom.ker f = 𝔓 := by
  -- proof
  classical
  let _ := h𝔓
  set D := T ⧸ 𝔓 with hD
  let _ : IsDomain D := Ideal.Quotient.isDomain 𝔓
  have hinjD : Function.Injective (algebraMap ℤ D) := by
    intro a b hab
    have h : ((a - b : ℤ) : T) ∈ 𝔓 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast, Int.cast_sub, sub_eq_zero]
      simpa [Algebra.algebraMap_eq_smul_one] using hab
    refine sub_eq_zero.mp (hint _ h)
  let _ : CharZero D := by
    refine ⟨fun a b hab => ?_⟩
    have hmap := hinjD (show algebraMap ℤ D (a : ℤ) = algebraMap ℤ D (b : ℤ) by simpa using hab)
    exact_mod_cast hmap
  let _ : @Module.IsTorsionFree ℤ D _ _ Algebra.toModule := by
    refine ⟨fun n hn => ?_⟩
    intro a b hab
    have hn0 : algebraMap ℤ D n ≠ 0 := (map_ne_zero_iff _ hinjD).mpr hn.ne_zero
    have h' : algebraMap ℤ D n * a = algebraMap ℤ D n * b := by
      simpa [Algebra.smul_def] using hab
    refine mul_left_cancel₀ hn0 h'
  let _ : Module.Finite ℤ D := Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ 𝔓).toLinearMap (Ideal.Quotient.mkₐ_surjective ℤ 𝔓)
  let _ : Algebra.IsIntegral ℤ D := inferInstance
  let _ : Algebra.IsAlgebraic ℤ D := ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  let φ : AlgHom ℤ D ℂ := IsAlgClosed.lift
  have hφker : RingHom.ker φ.toRingHom = ⊥ := by
    refine Ideal.eq_bot_of_under_eq_bot (R := ℤ) ?_
    refine eq_bot_iff.mpr fun n hn => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes] at hn
    simpa using hn
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro d hd
    have hker : d ∈ RingHom.ker φ.toRingHom := hd
    rw [hφker, Ideal.mem_bot] at hker
    apply hker
  have hmem : ∀ t : T, (φ.toRingHom.comp (Ideal.Quotient.mk 𝔓)) t ∈ integralClosure ℤ ℂ := fun t => (Algebra.IsIntegral.isIntegral (R := ℤ) (Ideal.Quotient.mk 𝔓 t)).map φ
  refine ⟨(φ.toRingHom.comp (Ideal.Quotient.mk 𝔓)).codRestrict (integralClosure ℤ ℂ) hmem, ?_⟩
  ext t
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  ·
    intro h
    apply hφinj
    rw [map_zero]
    apply congrArg Subtype.val h
  ·
    intro h
    apply Subtype.ext
    change φ (Ideal.Quotient.mk 𝔓 t) = 0
    rw [h, map_zero]


-- created on 2026-10-20
