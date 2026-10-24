import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma eq_zero_of_forall_dvd {ι : Type*} [Fintype ι] (p : ℕ) (hp : 1 < p) (P : (ι → ℤ) → Prop) (hP : ∀ g : ι → ℤ, P g → (∀ i, (p : ℤ) ∣ g i)) (hdiv : ∀ g : ι → ℤ, P (fun i => (p : ℤ) * g i) → P g) : ∀ g : ι → ℤ, P g → g = 0 := by
  suffices h : ∀ (N : ℕ) (g : ι → ℤ), (∑ i, (g i).natAbs) ≤ N → P g → g = 0 from
    fun g hg => h _ g le_rfl hg
  intro N
  induction N
  ·
    intro g hN _
    funext i
    apply Int.natAbs_eq_zero.mp (Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hN) i (Finset.mem_univ i))
  ·
    rename_i N ih
    intro g hN hg
    if hg0 : g = 0 then
      apply hg0
    else
      have hall := hP g hg
      choose g' hg' using hall
      have hgg' : g = fun i => (p : ℤ) * g' i := funext hg'
      have hPg' : P g' := hdiv g' (hgg' ▸ hg)
      have hlt : (∑ i, (g' i).natAbs) < ∑ i, (g i).natAbs := by
        have hle : ∀ i ∈ Finset.univ, (g' i).natAbs ≤ (g i).natAbs := by
          intro i _
          rw [hg' i, Int.natAbs_mul, Int.natAbs_natCast]
          apply Nat.le_mul_of_pos_left _ (by omega)
        obtain ⟨i₀, hi₀⟩ : ∃ i, g i ≠ 0 := by
          by_contra h
          push Not at h
          apply hg0 (funext h)
        refine Finset.sum_lt_sum hle ⟨i₀, Finset.mem_univ _, ?_⟩
        have hg'i : g' i₀ ≠ 0 := by
          intro h
          apply hi₀
          rw [hg' i₀, h, mul_zero]
        rw [hg' i₀, Int.natAbs_mul, Int.natAbs_natCast]
        have : 0 < (g' i₀).natAbs := Int.natAbs_pos.mpr hg'i
        nlinarith
      have := ih g' (by omega) hPg'
      rw [hgg', this]
      funext i
      simp
/--
[IsDiscreteValuationRing_finite_quotient_maximalIdeal_of_isFractionRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDiscreteValuationRing_finite_quotient_maximalIdeal_of_isFractionRing.lean)
-/
@[path]
private lemma main
  (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (L : Type*) [Field L] [CharZero L] [Algebra A L] [IsFractionRing A L] [FiniteDimensional ℚ L]
  (p : ℕ) [Fact p.Prime]
  -- given
  (hAp : (p : A) ∈ maximalIdeal A) :
  -- imply
  Finite (A ⧸ maximalIdeal A) := by
  -- proof
  classical
  set κ := A ⧸ maximalIdeal A
  have hp : p.Prime := Fact.out
  have hpκ : (p : κ) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal A)) p, Ideal.Quotient.eq_zero_iff_mem]
    apply hAp
  let _ : CharP κ p := by
    obtain ⟨ℓ, hℓ⟩ := CharP.exists κ
    have hdvd : ℓ ∣ p := (CharP.cast_eq_zero_iff κ ℓ p).mp hpκ
    have hprime : ℓ.Prime ∨ ℓ = 0 := CharP.char_is_prime_or_zero κ ℓ
    if hℓp : ℓ.Prime then
      have : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓp hp).mp hdvd
      subst this
      apply hℓ
    else
      have h0 : ℓ = 0 := hprime.resolve_left hℓp
      subst h0
      apply absurd (zero_dvd_iff.mp hdvd) hp.ne_zero
  let _ : Algebra (ZMod p) κ := ZMod.algebra κ p
  have key : ∀ s : Finset κ, LinearIndependent (ZMod p) ((↑) : s → κ) → s.card ≤ Module.finrank ℚ L := by
    intro s hs
    choose a ha using fun i : s => Ideal.Quotient.mk_surjective (I := maximalIdeal A) (i : κ)
    set x : s → L := fun i => algebraMap A L (a i) with hx
    have hinj : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
    have hZ : LinearIndependent ℤ x := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have := eq_zero_of_forall_dvd p hp.one_lt (fun g : s → ℤ => ∑ i, g i • x i = 0) ?_ ?_ g hg
      ·
        intro i
        apply congrFun this i
      ·
        intro g hg i
        have hA : ∑ i, (g i : A) * a i = 0 := by
          apply hinj
          rw [map_sum, map_zero]
          simp only [hx, zsmul_eq_mul] at hg
          simp only [map_mul, map_intCast]
          apply hg
        have hκ' : ∑ i, ((g i : ℤ) : ZMod p) • ((i : s) : κ) = 0 := by
          have := congrArg (Ideal.Quotient.mk (maximalIdeal A)) hA
          rw [map_sum, map_zero] at this
          refine (Finset.sum_congr rfl fun i _ => ?_).symm.trans this
          rw [map_mul, map_intCast, ha, Algebra.smul_def, map_intCast]
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd (g i) p).mp ((Fintype.linearIndependent_iff.mp hs) (fun i => ((g i : ℤ) : ZMod p)) hκ' i)
      ·
        intro g hg
        have : (p : L) • ∑ i, g i • x i = 0 := by
          rw [Finset.smul_sum]
          refine (Finset.sum_congr rfl fun i _ => ?_).trans hg
          simp only [zsmul_eq_mul, smul_eq_mul]
          push_cast
          ring
        apply (smul_eq_zero.mp this).resolve_left (Nat.cast_ne_zero.mpr hp.ne_zero)
    refine (Fintype.card_coe s).symm.trans_le ((LinearIndependent.iff_fractionRing ℤ ℚ).mp hZ).fintype_card_le_finrank
  have hrank : Module.rank (ZMod p) κ ≤ Module.finrank ℚ L := rank_le key
  let _ : Module.Finite (ZMod p) κ := Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0)
  apply Module.finite_of_finite (ZMod p)


-- created on 2026-10-20
