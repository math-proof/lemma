import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma FrobChareqEngine.engine1a
  [CommRing T] [Module.Finite ℤ T]
  {𝔓 : Ideal T}
  -- given
  (h𝔓 : 𝔓.IsPrime)
  (hint : ∀ n : ℤ, (n : T) ∈ 𝔓 → n = 0) :
  -- imply
  ∃ f : T →+* integralClosure ℤ ℂ, RingHom.ker f = 𝔓 := by
  -- proof
  classical
  let _ := h𝔓
  set D := T ⧸ 𝔓 with hD
  let _ : IsDomain D := Ideal.Quotient.isDomain 𝔓
  have hinjD : Function.Injective (algebraMap ℤ D) := by
    intro a b hab
    apply Iff.mp sub_eq_zero (hint _ _)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast, Int.cast_sub, sub_eq_zero]
    simpa [Algebra.algebraMap_eq_smul_one] using hab
  let _ : CharZero D := by
    refine ⟨fun a b hab => ?_⟩
    have := hinjD (show algebraMap ℤ D (a : ℤ) = algebraMap ℤ D (b : ℤ) by simpa using hab)
    exact_mod_cast this
  let _ : @Module.IsTorsionFree ℤ D _ _ Algebra.toModule := by
    refine ⟨fun n hn => ?_⟩
    intro a b hab
    apply mul_left_cancel₀ (Iff.mpr (map_ne_zero_iff _ hinjD) hn.ne_zero) _
    simpa only [Algebra.smul_def] using hab
  let _ : Module.Finite ℤ D := Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ 𝔓).toLinearMap (Ideal.Quotient.mkₐ_surjective ℤ 𝔓)
  let _ : Algebra.IsIntegral ℤ D := inferInstance
  let _ : Algebra.IsAlgebraic ℤ D := ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  let φ : D →ₐ[ℤ] ℂ := IsAlgClosed.lift
  have hφker : RingHom.ker φ.toRingHom = ⊥ := by
    refine Ideal.eq_bot_of_under_eq_bot (R := ℤ) ?_
    refine Iff.mpr eq_bot_iff fun n hn => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes] at hn
    simpa using hn
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro d hd
    have : d ∈ RingHom.ker φ.toRingHom := hd
    rw [hφker, Ideal.mem_bot] at this
    apply this
  have hmem : ∀ t : T, (φ.toRingHom.comp (Ideal.Quotient.mk 𝔓)) t ∈ integralClosure ℤ ℂ := by
    intro t
    apply (Algebra.IsIntegral.isIntegral (R := ℤ) (Ideal.Quotient.mk 𝔓 t)).map φ
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
    show φ (Ideal.Quotient.mk 𝔓 t) = 0
    rw [h, map_zero]

/--
[Ideal_exists_ringHom_integralClosure_comap_eq_of_isMaximal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_exists_ringHom_integralClosure_comap_eq_of_isMaximal.lean)
-/
@[path]
private lemma main
  [CommRing T] [IsAddTorsionFree T] [Module.Finite ℤ T]
  {𝔪 : Ideal T}
  -- given
  (h𝔪 : 𝔪.IsMaximal) :
  -- imply
  ∃ (f : T →+* integralClosure ℤ ℂ) (𝔐 : Ideal (integralClosure ℤ ℂ)), 𝔐.IsMaximal ∧ 𝔐.comap f = 𝔪 := by
  -- proof
  classical
  let _ := h𝔪
  obtain ⟨𝔓, h𝔓min, h𝔓le⟩ := Ideal.exists_minimalPrimes_le (show (⊥ : Ideal T) ≤ 𝔪 from bot_le)
  let h𝔓 : 𝔓.IsPrime := h𝔓min.1.1
  have hint : ∀ n : ℤ, (n : T) ∈ 𝔓 → n = 0 := by
    intro n hn
    by_contra hne
    suffices hreg : (n : T) ∈ nonZeroDivisors T by
      apply Iff.mp Set.disjoint_left (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes h𝔓min) hn hreg
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    apply Module.IsTorsionFree.isSMulRegular (IsRegular.of_ne_zero hne)
    show n • x = n • (0 : T)
    rw [smul_zero, zsmul_eq_mul, mul_comm, hx]
  obtain ⟨g, hgker⟩ := FrobChareqEngine.engine1a (𝔓 := 𝔓) h𝔓 hint
  let _ : Algebra T (integralClosure ℤ ℂ) := g.toAlgebra
  let _ : IsScalarTower ℤ T (integralClosure ℤ ℂ) := IsScalarTower.of_algebraMap_eq fun n => by
    show (n : integralClosure ℤ ℂ) = g (n : T)
    rw [map_intCast]
  let _ : Algebra.IsIntegral T (integralClosure ℤ ℂ) := ⟨fun x => (Algebra.IsIntegral.isIntegral (R := ℤ) x).tower_top⟩
  have hle : RingHom.ker (algebraMap T (integralClosure ℤ ℂ)) ≤ 𝔪 := by
    show RingHom.ker g ≤ 𝔪
    rw [hgker]
    apply h𝔓le
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔪 hle
  refine ⟨g, Q, hQmax, hQ⟩


-- created on 2026-10-20
