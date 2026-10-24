import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_FLTPrelim_FreyPackage
open FreyPackage
open WeierstrassCurve


noncomputable def c₄Int (P : FreyPackage) : ℤ :=
  (P.a ^ P.p) ^ 2 + P.a ^ P.p * P.b ^ P.p + (P.b ^ P.p) ^ 2

private lemma freyCurveInt_map (P : FreyPackage) :
  (freyCurveInt P).map (algebraMap ℤ ℚ) = freyCurve P := by
  have two_dvd_b : 2 ∣ P.b := (ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).1 P.hb2
  ext
  · rfl
  ·
    change (((P.b ^ P.p - 1 - P.a ^ P.p) / 4 : ℤ) : ℚ) = (P.b ^ P.p - 1 - P.a ^ P.p) / 4
    rw [Rat.intCast_div]
    · norm_cast
    ·
      rw [sub_sub]
      apply Int.dvd_sub
      ·
        calc
          _ = 2 ^ 2 := by norm_num
          _ ∣ P.b ^ 2 := pow_dvd_pow_of_dvd two_dvd_b 2
          _ ∣ P.b ^ P.p := pow_dvd_pow P.b (by linarith [P.hp5])
      ·
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1
        push_cast
        rw [P.ha4, show (3 : ZMod 4) = -1 from rfl, neg_one_pow_eq_ite, ite_eq_right]
        · norm_num
        ·
          rw [Nat.Prime.even_iff P.pp]
          linarith [P.hp5]
  · rfl
  ·
    change ((-(P.a ^ P.p) * (P.b ^ P.p) / 16 : ℤ) : ℚ) = -(P.a ^ P.p) * (P.b ^ P.p) / 16
    rw [Rat.intCast_div]
    · norm_cast
    ·
      calc
        _ = 2 ^ 4 := by norm_num
        _ ∣ P.b ^ 4 := pow_dvd_pow_of_dvd two_dvd_b 4
        _ ∣ P.b ^ P.p := pow_dvd_pow P.b (by linarith [P.hp5])
        _ ∣ _ := Int.dvd_mul_left _ _
  · rfl

private lemma freyCurve_Δ (P : FreyPackage) :
  P.freyCurve.Δ = (P.a * P.b * P.c) ^ (2 * P.p) / 2 ^ 8 := by
  trans (P.a ^ P.p) ^ 2 * (P.b ^ P.p) ^ 2 * (P.c ^ P.p) ^ 2 / 2 ^ 8
  ·
    field_simp
    norm_cast
    simp [← P.hFLT, WeierstrassCurve.Δ, freyCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  · simp [← mul_pow, ← pow_mul, mul_comm 2]

private lemma freyCurve_c₄_eq_intCast (P : FreyPackage) : P.freyCurve.c₄ = (c₄Int P : ℚ) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, freyCurve, c₄Int]
  push_cast
  field_simp
  ring

private lemma c₄Int_eq_sub (P : FreyPackage) : c₄Int P = (P.c ^ P.p) ^ 2 - (P.a * P.b) ^ P.p := by
  rw [c₄Int, ← P.hFLT, mul_pow]
  ring

private lemma not_dvd_c₄Int (P : FreyPackage) {q : ℤ} (hq : Prime q) (hqbad : q ∣ P.a * P.b * P.c) : ¬q ∣ c₄Int P := by
  intro hdvd
  refine Or.elim (hq.dvd_mul.mp hqbad) ?_ ?_
  ·
    intro hab
    refine Or.elim (hq.dvd_mul.mp hab) ?_ ?_
    ·
      intro ha
      have hqb : ¬q ∣ P.b := fun hb =>
        hq.not_unit (isUnit_of_dvd_one (P.hgcdab ▸ dvd_gcd ha hb))
      have hqap : q ∣ P.a ^ P.p := dvd_pow ha P.hp0
      rw [c₄Int, dvd_add_right (dvd_add (dvd_pow hqap two_ne_zero)
        (dvd_mul_of_dvd_left hqap _))] at hdvd
      exact hqb (hq.dvd_of_dvd_pow (hq.dvd_of_dvd_pow hdvd))
    ·
      intro hb
      have hqa : ¬q ∣ P.a := fun ha =>
        hq.not_unit (isUnit_of_dvd_one (P.hgcdab ▸ dvd_gcd ha hb))
      have hqbp : q ∣ P.b ^ P.p := dvd_pow hb P.hp0
      rw [c₄Int, add_assoc, dvd_add_left (dvd_add (dvd_mul_of_dvd_right hqbp _)
        (dvd_pow hqbp two_ne_zero))] at hdvd
      exact hqa (hq.dvd_of_dvd_pow (hq.dvd_of_dvd_pow hdvd))
  ·
    intro hc
    have hqa : ¬q ∣ P.a := fun ha =>
      hq.not_unit (isUnit_of_dvd_one (P.hgcdac ▸ dvd_gcd ha hc))
    have hqb : ¬q ∣ P.b := fun hb =>
      hq.not_unit (isUnit_of_dvd_one (P.hgcdbc ▸ dvd_gcd hb hc))
    rw [c₄Int_eq_sub, dvd_sub_right (dvd_pow (dvd_pow hc P.hp0) two_ne_zero)] at hdvd
    refine Or.elim (hq.dvd_mul.mp (hq.dvd_of_dvd_pow hdvd)) ?_ ?_
    ·
      intro h
      exact hqa h
    ·
      intro h
      exact hqb h

private lemma freyCurveInt_c₄ (P : FreyPackage) : (freyCurveInt P).c₄ = c₄Int P := by
  have h : (algebraMap ℤ ℚ) (freyCurveInt P).c₄ = ((c₄Int P : ℤ) : ℚ) := by
    rw [← map_c₄, freyCurveInt_map, ← freyCurve_c₄_eq_intCast]
  rw [eq_intCast] at h
  exact_mod_cast h

private lemma freyCurveInt_Δ_mul (P : FreyPackage) :
  (freyCurveInt P).Δ * 2 ^ 8 = (P.a * P.b * P.c) ^ (2 * P.p) := by
  have hΔ : (algebraMap ℤ ℚ) (freyCurveInt P).Δ = (P.a * P.b * P.c : ℚ) ^ (2 * P.p) / 2 ^ 8 := by
    rw [← map_Δ, freyCurveInt_map, freyCurve_Δ]
  rw [eq_intCast] at hΔ
  have h : ((((freyCurveInt P).Δ * 2 ^ 8 : ℤ)) : ℚ) = (((P.a * P.b * P.c) ^ (2 * P.p) : ℤ) : ℚ) := by
    push_cast
    rw [hΔ]
    field_simp
    norm_num
  exact_mod_cast h

private lemma freyCurveInt_Δ_ne_zero (P : FreyPackage) : (freyCurveInt P).Δ ≠ 0 := by
  intro h
  have := freyCurveInt_Δ_mul P
  rw [h, zero_mul] at this
  exact pow_ne_zero _ P.habc0 this.symm

private lemma dvd_abc_of_dvd_freyCurveInt_Δ (P : FreyPackage) {q : ℕ} (hq : q.Prime) (hdvd : (q : ℤ) ∣ (freyCurveInt P).Δ) : (q : ℤ) ∣ P.a * P.b * P.c :=
  (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow (n := 2 * P.p)
    (freyCurveInt_Δ_mul P ▸ hdvd.mul_right (2 ^ 8))

private lemma padicValInt_freyCurveInt_Δ (P : FreyPackage) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
  padicValInt q (freyCurveInt P).Δ = 2 * P.p * padicValInt q (P.a * P.b * P.c) := by
  have : Fact q.Prime := ⟨hq⟩
  have hq28 : ¬ (q : ℤ) ∣ 2 ^ 8 := by
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (by exact_mod_cast ((Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow h)))
  have hmul : padicValInt q ((freyCurveInt P).Δ * 2 ^ 8) = padicValInt q (freyCurveInt P).Δ := by
    rw [padicValInt.mul (freyCurveInt_Δ_ne_zero P) (by norm_num),
      padicValInt.eq_zero_of_not_dvd hq28, add_zero]
  rw [← hmul, freyCurveInt_Δ_mul]
  simp only [padicValInt, Int.natAbs_pow]
  exact padicValNat.pow _ _
/--
[FreyPackage_padicValInt_freyCurveInt_discr](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_padicValInt_freyCurveInt_discr.lean)
-/
@[path]
private lemma main
  {P : FreyPackage}
  {q : ℕ}
-- given
  (hq : q.Prime)
  (hq2 : q ≠ 2) :
-- imply
  padicValInt q P.freyCurveInt.Δ = 2 * P.p * padicValInt q (P.a * P.b * P.c) :=
-- proof
  padicValInt_freyCurveInt_Δ P hq hq2


-- created on 2026-10-23
