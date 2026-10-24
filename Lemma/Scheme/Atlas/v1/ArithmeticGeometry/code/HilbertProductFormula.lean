import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.HilbertProductFormula
open HilbertSymbol


/--
[ratToRealUnits_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma ratToRealUnits_val
  {a : ℚˣ} :
-- imply
  (ratToRealUnits a : ℝ) = ((a : ℚ) : ℝ) :=
-- proof
  rfl

/--
[ratToQpUnits_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma ratToQpUnits_val
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a : ℚˣ} :
-- imply
  (ratToQpUnits p a : ℚ_[p]) = ((a : ℚ) : ℚ_[p]) :=
-- proof
  rfl

/--
[ratToRealUnits_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma ratToRealUnits_mul
  {a b : ℚˣ} :
-- imply
  ratToRealUnits (a * b) = ratToRealUnits a * ratToRealUnits b := by
-- proof
  ext; simp [ratToRealUnits]

/--
[ratToQpUnits_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma ratToQpUnits_mul
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚˣ} :
-- imply
  ratToQpUnits p (a * b) = ratToQpUnits p a * ratToQpUnits p b := by
-- proof
  ext; simp [ratToQpUnits]

/--
[ratToQpUnits_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma ratToQpUnits_neg_one
  {p : ℕ}
  [Fact (Nat.Prime p)] :
-- imply
  ratToQpUnits p (-1 : ℚˣ) = unitZpToQp (-1 : ℤ_[p]ˣ) := by
-- proof
  ext
  simp [ratToQpUnits, unitZpToQp_coe]

/--
[hilbertAtPrime_neg_one_neg_one_odd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbertAtPrime_neg_one_neg_one_odd
  {p : ℕ}
  [Fact (Nat.Prime p)]
-- given
  (hp : p ≠ 2) :
-- imply
  hilbertAtPrime p (-1) (-1) = 1 := by
-- proof
  unfold hilbertAtPrime
  rw [show ratToQpUnits p (-1 : ℚˣ) = unitZpToQp (-1 : ℤ_[p]ˣ) from
    ratToQpUnits_neg_one p]
  exact hilbert_symbol_units_eq_one_of_odd p hp (-1) (-1)

/--
[ratToQpUnits_neg_one_eq_padicUnit_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma ratToQpUnits_neg_one_eq_padicUnit_one
-- imply
  ratToQpUnits 2 (-1 : ℚˣ) = padicUnit_one (-1 : ℤ_[2]ˣ) := by
-- proof
  ext
  simp [ratToQpUnits, padicUnit_one_val]

/--
[hilbertAtPrime_neg_one_neg_one_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbertAtPrime_neg_one_neg_one_two
-- imply
  hilbertAtPrime 2 (-1) (-1) = -1 := by
-- proof
  unfold hilbertAtPrime
  rw [show ratToQpUnits 2 (-1 : ℚˣ) = padicUnit_one (-1 : ℤ_[2]ˣ) from
    ratToQpUnits_neg_one_eq_padicUnit_one]
  rw [thm_10_9_one_one]
  have hunit : toZModPow_unit 3 (-1 : ℤ_[2]ˣ) = (-1 : (ZMod (2 ^ 3))ˣ) := by
    ext
    rw [toZModPow_unit_coe]
    simp [PadicInt.toZModPow]
  rw [hunit]
  native_decide

/--
[hilbertAtInfty_neg_one_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbertAtInfty_neg_one_neg_one
-- imply
  hilbertAtInfty (-1) (-1) = -1 := by
-- proof
  unfold hilbertAtInfty
  rw [realHilbertSymbol.eq_neg_one_iff_both_neg]
  exact ⟨by simp [ratToRealUnits], by simp [ratToRealUnits]⟩

/--
[ratToQpUnits_eq_unitZpToQp_of_not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma ratToQpUnits_eq_unitZpToQp_of_not_dvd
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a : ℚˣ}
-- given
  (hnum : ¬ (p : ℕ) ∣ (a : ℚ).num.natAbs)
  (hden : ¬ (p : ℕ) ∣ (a : ℚ).den) :
-- imply
  ∃ u : ℤ_[p]ˣ, ratToQpUnits p a = unitZpToQp u := by
-- proof
  have hq : (a : ℚ) ≠ 0 := a.ne_zero
  have hpn : padicNorm p (a : ℚ) = 1 := by
    rw [padicNorm.eq_zpow_of_nonzero hq, padicValRat_def,
      padicValInt.eq_zero_of_not_dvd (by rwa [Int.natCast_dvd]),
      padicValNat.eq_zero_of_not_dvd hden]
    simp
  have hnorm : ‖((a : ℚ) : ℚ_[p])‖ = 1 := by
    rw [Padic.eq_padicNorm]
    exact_mod_cast hpn
  have hle : ‖((a : ℚ) : ℚ_[p])‖ ≤ 1 := le_of_eq hnorm
  let z : ℤ_[p] := ⟨((a : ℚ) : ℚ_[p]), hle⟩
  have hz : IsUnit z := PadicInt.isUnit_iff.mpr (by rwa [PadicInt.norm_def])
  refine ⟨hz.unit, Units.ext ?_⟩
  simp only [ratToQpUnits_val]
  rw [unitZpToQp_coe]
  simp [z, IsUnit.unit_spec]

/--
[ratToQpUnits_two_eq_twoQp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma ratToQpUnits_two_eq_twoQp
-- imply
  ratToQpUnits 2 (Units.mk0 (2 : ℚ) (by norm_num)) = twoQp := by
-- proof
  ext
  simp only [ratToQpUnits_val, Units.val_mk0, Rat.cast_ofNat, twoQp_val]

/--
[ratToQpUnits_natPrime_eq_qpPrime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma ratToQpUnits_natPrime_eq_qpPrime
  {q : ℕ}
  [Fact (Nat.Prime q)] :
-- imply
  ratToQpUnits q (Units.mk0 (q : ℚ) (by exact_mod_cast (Fact.out : Nat.Prime q).ne_zero)) = qpPrime q := by
-- proof
  ext
  simp only [ratToQpUnits_val, Units.val_mk0, qpPrime]
  push_cast
  rfl

/--
[ratToQpUnits_two_at_odd_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma ratToQpUnits_two_at_odd_prime
  {p : ℕ}
  [Fact (Nat.Prime p)]
-- given
  (hp : p ≠ 2) :
-- imply
  ∃ u : ℤ_[p]ˣ, ratToQpUnits p (Units.mk0 (2 : ℚ) (by norm_num)) = unitZpToQp u := by
-- proof
  apply ratToQpUnits_eq_unitZpToQp_of_not_dvd
  ·
    simp only [Units.val_mk0]
    norm_num
    have : 2 < p := by have := (Fact.out : Nat.Prime p).two_le; omega
    exact fun h => Nat.not_lt.mpr (Nat.le_of_dvd (by norm_num) h) this
  ·
    simp only [Units.val_mk0]
    norm_num
    exact (Fact.out : Nat.Prime p).one_lt.ne'

/--
[ratToQpUnits_prime_at_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma ratToQpUnits_prime_at_two
  {q : ℕ}
-- given
  (hq : Nat.Prime q)
  (hq_odd : q ≠ 2) :
-- imply
  haveI : Fact (Nat.Prime 2) :=
-- proof
  ⟨by decide⟩
    ∃ u : ℤ_[2]ˣ, ratToQpUnits 2 (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) =
      unitZpToQp u := by
    apply ratToQpUnits_eq_unitZpToQp_of_not_dvd
    ·
      simp only [Units.val_mk0, Rat.num_natCast, Int.natAbs_natCast]
      intro h
      have := hq.eq_one_or_self_of_dvd 2 h
      omega
    ·
      simp only [Units.val_mk0, Rat.den_natCast]
      omega

/--
[hilbert_product_formula_finite_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbert_product_formula_finite_support
  {a b : ℚˣ} :
-- imply
  Set.Finite {p : Nat.Primes | haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩ hilbertAtPrime p.val a b ≠ 1} := by
-- proof
  let N := 2 * (a : ℚ).num.natAbs * (a : ℚ).den * ((b : ℚ).num.natAbs * (b : ℚ).den)
  have hN : N ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    apply mul_ne_zero
    · omega
    · exact (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr a.ne_zero)).ne'
    · exact a.val.den_pos.ne'
    · exact mul_ne_zero (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr b.ne_zero)).ne' b.val.den_pos.ne'
  have hfin : Set.Finite {p : Nat.Primes | p.val ∣ N} :=
    Set.Finite.subset
      (Set.Finite.preimage (fun a _ b _ hab => Subtype.val_injective hab)
        (Nat.divisors N).finite_toSet)
      (fun p hp => by
        simp only [Set.mem_preimage, Finset.mem_coe, Nat.mem_divisors] at *
        exact ⟨hp, hN⟩)
  apply hfin.subset
  intro ⟨p_val, hp_prime⟩ hmem
  simp only [Set.mem_setOf_eq] at hmem ⊢
  by_contra h_not_dvd
  apply hmem
  haveI : Fact (Nat.Prime p_val) := ⟨hp_prime⟩
  have h_no_factor : ¬ (p_val ∣ 2) ∧ ¬ (p_val ∣ (a : ℚ).num.natAbs) ∧
    ¬ (p_val ∣ (a : ℚ).den) ∧ ¬ (p_val ∣ (b : ℚ).num.natAbs) ∧ ¬ (p_val ∣ (b : ℚ).den) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> apply h_not_dvd
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _
    · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h _) _
    · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h _) _
  obtain ⟨h2, hnd, hdd, hnb, hdb⟩ := h_no_factor
  have hp2 : p_val ≠ 2 := fun h => h2 (h ▸ dvd_refl p_val)
  obtain ⟨ua, hua⟩ := ratToQpUnits_eq_unitZpToQp_of_not_dvd p_val a hnd hdd
  obtain ⟨ub, hub⟩ := ratToQpUnits_eq_unitZpToQp_of_not_dvd p_val b hnb hdb
  unfold hilbertAtPrime
  rw [hua, hub]
  exact hilbert_symbol_units_eq_one_of_odd p_val hp2 ua ub

/--
[hilbert_product_neg_one_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbert_product_neg_one_neg_one
-- imply
  globalHilbertProduct (-1) (-1) = 1 := by
-- proof
  unfold globalHilbertProduct
  let f : Nat.Primes → ℤ := fun p =>
    haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
    hilbertAtPrime p.val (-1) (-1)
  suffices h : hilbertAtInfty (-1) (-1) * ∏ᶠ (p : Nat.Primes), f p = 1 by
    convert h
  have h2 : Nat.Prime 2 := by decide
  let two : Nat.Primes := ⟨2, h2⟩
  have hsupp : Function.mulSupport f ⊆ ↑({two} : Finset Nat.Primes) := by
    intro p hp
    simp only [Finset.coe_singleton, Set.mem_singleton_iff]
    rw [Function.mem_mulSupport] at hp
    by_contra hne
    apply hp
    have hp2 : p.val ≠ 2 := by
      intro h
      exact hne (Subtype.ext h)
    haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
    exact hilbertAtPrime_neg_one_neg_one_odd p.val hp2
  rw [finprod_eq_prod_of_mulSupport_subset f hsupp]
  simp only [Finset.prod_singleton]
  show hilbertAtInfty (-1) (-1) * f two = 1
  simp only [f, two]
  rw [hilbertAtInfty_neg_one_neg_one, hilbertAtPrime_neg_one_neg_one_two]
  norm_num

/--
[hilbert_product_neg_one_odd_prime_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbert_product_neg_one_odd_prime_aux
  {q : ℕ}
-- given
  (hq : Nat.Prime q)
  (hq_odd : q ≠ 2) :
-- imply
  haveI : Fact (Nat.Prime q) :=
-- proof
  ⟨hq⟩
    globalHilbertProduct (-1) (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1 := by
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    let b : ℚˣ := Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)
    show globalHilbertProduct (-1) b = 1
    unfold globalHilbertProduct
    let f : Nat.Primes → ℤ := fun p =>
      haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
      hilbertAtPrime p.val (-1) b
    suffices h : hilbertAtInfty (-1) b * ∏ᶠ (p : Nat.Primes), f p = 1 by
      convert h
    have h2 : Nat.Prime 2 := by decide
    let two : Nat.Primes := ⟨2, h2⟩
    let q_prime : Nat.Primes := ⟨q, hq⟩
    have hneq : two ≠ q_prime := by
      intro h
      have : (2 : ℕ) = q := congr_arg Subtype.val h
      exact hq_odd this.symm
    have hsupp : Function.mulSupport f ⊆ ↑({two, q_prime} : Finset Nat.Primes) := by
      intro p hp
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      rw [Function.mem_mulSupport] at hp
      by_contra hne
      push_neg at hne
      apply hp
      have hp2 : p.val ≠ 2 := by
        intro h; exact hne.1 (Subtype.ext h)
      have hpq : p.val ≠ q := by
        intro h; exact hne.2 (Subtype.ext h)
      haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
      obtain ⟨u_neg1, hu_neg1⟩ : ∃ u : ℤ_[p.val]ˣ, ratToQpUnits p.val (-1 : ℚˣ) = unitZpToQp u :=
        ⟨-1, ratToQpUnits_neg_one p.val⟩
      have hpq_dvd : ¬ (p.val ∣ q) := by
        intro h
        have := hq.eq_one_or_self_of_dvd p.val h
        obtain h1 | h1 := this
        · exact p.property.one_lt.ne' h1
        · exact absurd h1 hpq
      obtain ⟨u_q, hu_q⟩ := ratToQpUnits_eq_unitZpToQp_of_not_dvd p.val b
        (by simp only [b, Units.val_mk0, Rat.num_natCast, Int.natAbs_natCast]; exact hpq_dvd)
        (by simp only [b, Units.val_mk0, Rat.den_natCast]
          exact Nat.Prime.not_dvd_one p.property)
      show f p = 1
      simp only [f]
      unfold hilbertAtPrime
      rw [hu_neg1, hu_q]
      exact hilbert_symbol_units_eq_one_of_odd p.val hp2 u_neg1 u_q
    rw [finprod_eq_prod_of_mulSupport_subset f hsupp]
    simp only [Finset.prod_pair hneq]
    show hilbertAtInfty (-1) b * (f two * f q_prime) = 1
    simp only [f, two, q_prime]
    have hinfty : hilbertAtInfty (-1) b = 1 := by
      unfold hilbertAtInfty
      rw [realHilbertSymbol.eq_one_iff]
      exact realHilbertSymbol.isSolvable_of_pos_right (by
        simp only [b, ratToRealUnits_val, Units.val_mk0]
        exact_mod_cast hq.pos)
    rw [hinfty, one_mul]
    have hf_q : hilbertAtPrime q (-1) b = padicUnitLegendre (-1 : ℤ_[q]ˣ) := by
      unfold hilbertAtPrime
      rw [ratToQpUnits_neg_one q, ratToQpUnits_natPrime_eq_qpPrime q]
      show padicHilbertSymbol q (unitZpToQp (-1 : ℤ_[q]ˣ)) (qpPrime q) = padicUnitLegendre (-1 : ℤ_[q]ˣ)
      rw [show padicHilbertSymbol q (unitZpToQp (-1 : ℤ_[q]ˣ)) (qpPrime q) =
        padicHilbertSymbol q (qpPrime q) (unitZpToQp (-1 : ℤ_[q]ˣ)) from
        hilbertSymbol.symm (unitZpToQp (-1)) (qpPrime q)]
      exact hilbert_p_unit_eq_legendre hq_odd (-1)
    have hleg_neg1 : padicUnitLegendre (-1 : ℤ_[q]ˣ) = legendreSym q (-1) := by
      have h_toZMod : PadicInt.toZMod ((-1 : ℤ_[q]ˣ) : ℤ_[q]) = (-1 : ZMod q) := by
        have : ((-1 : ℤ_[q]ˣ) : ℤ_[q]) = ((-1 : ℤ) : ℤ_[q]) := by simp
        rw [this]
        exact_mod_cast map_intCast PadicInt.toZMod (-1)
      unfold padicUnitLegendre legendreSym
      congr 1
      haveI : NeZero (q : ℕ) := ⟨hq.ne_zero⟩
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id', id, show (-1 : ℤ_[q]) = ↑(-1 : ℤ_[q]ˣ) from by simp, h_toZMod]
    obtain ⟨v, hv⟩ := ratToQpUnits_prime_at_two q hq hq_odd
    have hf_2 : hilbertAtPrime 2 (-1) b =
      hilbert2Adic_formula (toZModPow_unit 3 (-1 : ℤ_[2]ˣ)) (toZModPow_unit 3 v) 0 0 := by
      unfold hilbertAtPrime
      rw [ratToQpUnits_neg_one_eq_padicUnit_one]
      have hv_unit : ratToQpUnits 2 b = padicUnit_one v := by
        rw [hv]; ext; simp [unitZpToQp_coe, padicUnit_one_val]
      rw [hv_unit]
      exact thm_10_9_one_one (-1) v
    have hunit_neg1 : toZModPow_unit 3 (-1 : ℤ_[2]ˣ) = (-1 : (ZMod (2 ^ 3))ˣ) := by
      ext; rw [toZModPow_unit_coe]; simp [PadicInt.toZModPow]
    have hleg_2adic : hilbert2Adic_formula (toZModPow_unit 3 (-1 : ℤ_[2]ˣ)) (toZModPow_unit 3 v) 0 0 =
      legendreSym q (-1) := by
      rw [hunit_neg1]
      have h_formula_eq_chi4 : ∀ v₀ : (ZMod (2 ^ 3))ˣ,
        hilbert2Adic_formula (-1) v₀ 0 0 = ZMod.χ₄ ((v₀ : ZMod (2 ^ 3)).val : ZMod 4) := by
        native_decide
      rw [h_formula_eq_chi4]
      have h_v_eq_q : (toZModPow_unit 3 v : ZMod (2 ^ 3)) = ((q : ℤ) : ZMod (2 ^ 3)) := by
        rw [toZModPow_unit_coe]
        have h_Qp_eq : ((v : ℤ_[2]) : ℚ_[2]) = ((q : ℚ) : ℚ_[2]) := by
          have := congr_arg Units.val hv.symm
          rwa [unitZpToQp_coe, ratToQpUnits_val] at this
        have h_coe_eq : (v : ℤ_[2]) = ((q : ℤ) : ℤ_[2]) := by
          apply Subtype.coe_injective
          show ((v : ℤ_[2]) : ℚ_[2]) = (((q : ℤ) : ℤ_[2]) : ℚ_[2])
          rw [h_Qp_eq]; push_cast; ring
        rw [h_coe_eq]
        exact map_intCast (PadicInt.toZModPow 3) q
      have h_v_eq_q8 := show (↑(toZModPow_unit 3 v) : ZMod (2^3)) = ((q : ℤ) : ZMod (2^3)) from h_v_eq_q
      rw [h_v_eq_q8]
      rw [legendreSym.at_neg_one hq_odd]
      congr 1
      rw [show ((q : ℤ) : ZMod (2^3)) = ((q : ℕ) : ZMod (2^3)) from by push_cast; rfl]
      rw [ZMod.val_natCast, ZMod.natCast_eq_natCast_iff']
      omega
    rw [hf_2, hf_q, hleg_2adic, hleg_neg1]
    have hval := quadraticChar_isQuadratic (F := ZMod q) ((-1 : ℤ) : ZMod q)
    unfold legendreSym
    obtain h | h | h := hval
    · exfalso
      rw [quadraticChar_eq_zero_iff] at h
      have h_dvd : ((q : ℤ) ∣ -1) := (ZMod.intCast_zmod_eq_zero_iff_dvd (-1) q).mp (by push_cast at h ⊢; exact h)
      have hq_ge : (q : ℤ) ≥ 2 := by exact_mod_cast hq.two_le
      linarith [Int.le_of_dvd (by norm_num : (0 : ℤ) < 1) (dvd_neg.mp h_dvd)]
    · rw [h]; norm_num
    · rw [h]; norm_num

/--
[hilbertAtInfty_mul_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbertAtInfty_mul_left
  {a b c : ℚˣ} :
-- imply
  hilbertAtInfty (a * b) c = hilbertAtInfty a c * hilbertAtInfty b c := by
-- proof
  unfold hilbertAtInfty
  rw [ratToRealUnits_mul]
  exact hilbertSymbol.mul_left (ratToRealUnits a) (ratToRealUnits b) (ratToRealUnits c)

/--
[hilbertAtPrime_mul_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbertAtPrime_mul_left
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b c : ℚˣ} :
-- imply
  hilbertAtPrime p (a * b) c = hilbertAtPrime p a c * hilbertAtPrime p b c := by
-- proof
  unfold hilbertAtPrime
  rw [ratToQpUnits_mul]
  exact padic_hilbert_mul_left p (ratToQpUnits p a) (ratToQpUnits p b) (ratToQpUnits p c)

/--
[hilbertAtInfty_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbertAtInfty_comm
  {a b : ℚˣ} :
-- imply
  hilbertAtInfty a b = hilbertAtInfty b a := by
-- proof
  unfold hilbertAtInfty realHilbertSymbol
  simp only [hilbertSymbol.symm]

/--
[hilbertAtPrime_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbertAtPrime_comm
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a b : ℚˣ} :
-- imply
  hilbertAtPrime p a b = hilbertAtPrime p b a := by
-- proof
  unfold hilbertAtPrime padicHilbertSymbol
  exact hilbertSymbol.symm (ratToQpUnits p a) (ratToQpUnits p b)

/--
[globalHilbertProduct_mul_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma globalHilbertProduct_mul_left
  {a b c : ℚˣ} :
-- imply
  globalHilbertProduct (a * b) c = globalHilbertProduct a c * globalHilbertProduct b c := by
-- proof
  unfold globalHilbertProduct
  rw [hilbertAtInfty_mul_left]
  have hprod : (∏ᶠ (p : Nat.Primes),
    (haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩; hilbertAtPrime p.val (a * b) c)) =
    (∏ᶠ (p : Nat.Primes),
    (haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩; hilbertAtPrime p.val a c)) *
    (∏ᶠ (p : Nat.Primes),
    (haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩; hilbertAtPrime p.val b c)) := by
    have heq : (fun (p : Nat.Primes) =>
      (haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩; hilbertAtPrime p.val (a * b) c)) =
      (fun (p : Nat.Primes) =>
      (haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩; hilbertAtPrime p.val a c) *
      (haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩; hilbertAtPrime p.val b c)) := by
      ext p
      haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
      exact hilbertAtPrime_mul_left p.val a b c
    rw [heq]
    apply finprod_mul_distrib
    ·
      apply Set.Finite.subset (hilbert_product_formula_finite_support a c)
      intro p hp
      simp only [Set.mem_setOf_eq, Function.mem_mulSupport] at *
      exact hp
    ·
      apply Set.Finite.subset (hilbert_product_formula_finite_support b c)
      intro p hp
      simp only [Set.mem_setOf_eq, Function.mem_mulSupport] at *
      exact hp
  rw [hprod]
  ring

/--
[globalHilbertProduct_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma globalHilbertProduct_comm
  {a b : ℚˣ} :
-- imply
  globalHilbertProduct a b = globalHilbertProduct b a := by
-- proof
  unfold globalHilbertProduct
  rw [hilbertAtInfty_comm]
  congr 1
  apply finprod_congr
  intro p
  haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
  exact hilbertAtPrime_comm p.val a b

/--
[globalHilbertProduct_mul_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma globalHilbertProduct_mul_right
  {a b c : ℚˣ} :
-- imply
  globalHilbertProduct a (b * c) = globalHilbertProduct a b * globalHilbertProduct a c := by
-- proof
  rw [globalHilbertProduct_comm a (b * c), globalHilbertProduct_mul_left,
    globalHilbertProduct_comm b a, globalHilbertProduct_comm c a]

/--
[globalHilbertProduct_eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma globalHilbertProduct_eq_one_or_neg_one
  {a b : ℚˣ} :
-- imply
  globalHilbertProduct a b = 1 ∨ globalHilbertProduct a b = -1 := by
-- proof
  have mul_pm_one : ∀ x y : ℤ, (x = 1 ∨ x = -1) → (y = 1 ∨ y = -1) →
    (x * y = 1 ∨ x * y = -1) := by
    intros x y hx hy
    obtain rfl | rfl <;> rcases hy with rfl | rfl <;> simp := hx
  have hinfty : hilbertAtInfty a b = 1 ∨ hilbertAtInfty a b = -1 := by
    unfold hilbertAtInfty
    exact realHilbertSymbol.eq_one_or_neg_one _ _
  let f : Nat.Primes → ℤ := fun p =>
    haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
    hilbertAtPrime p.val a b
  have hf_pm : ∀ p : Nat.Primes, f p = 1 ∨ f p = -1 := by
    intro p
    haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
    simp only [f]
    unfold hilbertAtPrime
    exact padicHilbertSymbol.eq_one_or_neg_one _ _
  have hfin := hilbert_product_formula_finite_support a b
  have hsupp : (Function.mulSupport f).Finite := by
    apply Set.Finite.subset hfin
    intro p hp
    simp only [Set.mem_setOf_eq, Function.mem_mulSupport] at *
    exact hp
  have hfinprod_eq : ∏ᶠ (p : Nat.Primes), f p =
    hsupp.toFinset.prod f :=
    finprod_eq_prod_of_mulSupport_subset f (by
      intro p hp
      exact Finset.mem_coe.mpr (hsupp.mem_toFinset.mpr hp))
  suffices h : globalHilbertProduct a b = hilbertAtInfty a b * (∏ᶠ (p : Nat.Primes), f p) by
    rw [h, hfinprod_eq]
    suffices hprod : hsupp.toFinset.prod f = 1 ∨ hsupp.toFinset.prod f = -1 from
      mul_pm_one _ _ hinfty hprod
    have : ∀ (s : Finset Nat.Primes), (∀ x ∈ s, f x = 1 ∨ f x = -1) →
      s.prod f = 1 ∨ s.prod f = -1 := by
      intro s hs
      induction s using Finset.induction with
      | empty => simp
      | @insert p t hpt ih =>
        rw [Finset.prod_insert hpt]
        exact mul_pm_one _ _ (hs _ (Finset.mem_insert_self _ _))
          (ih (fun x hx => hs x (Finset.mem_insert_of_mem hx)))
    exact this _ (fun p _ => hf_pm p)
  rfl

/--
[globalHilbertProduct_one_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma globalHilbertProduct_one_left
  {b : ℚˣ} :
-- imply
  globalHilbertProduct 1 b = 1 := by
-- proof
  have h := globalHilbertProduct_mul_left 1 1 b
  simp only [one_mul] at h
  obtain h1 | h1 := globalHilbertProduct_eq_one_or_neg_one 1 b
  · exact h1
  ·
    rw [h1] at h; norm_num at h

/--
[globalHilbertProduct_generators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma globalHilbertProduct_generators
  {p q : ℕ}
-- given
  (h0 : globalHilbertProduct (-1) (-1) = 1)
  (h1 : ∀ q : ℕ, (hq : Nat.Prime q) → haveI : Fact (Nat.Prime q) := ⟨hq⟩ globalHilbertProduct (-1) (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1)
  (h2 : ∀ q : ℕ, (hq : Nat.Prime q) → haveI : Fact (Nat.Prime q) := ⟨hq⟩ let q' := Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero) globalHilbertProduct q' q' = 1)
  (h3 : ∀ q : ℕ, (hq : Nat.Prime q) → q ≠ 2 → haveI : Fact (Nat.Prime q) := ⟨hq⟩ globalHilbertProduct (Units.mk0 (2 : ℚ) (by norm_num)) (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1)
  (h4 : ∀ a b : ℕ, (ha : Nat.Prime a) → (hb : Nat.Prime b) → a ≠ 2 → b ≠ 2 → a ≠ b → haveI : Fact (Nat.Prime a) := ⟨ha⟩ haveI : Fact (Nat.Prime b) := ⟨hb⟩ globalHilbertProduct (Units.mk0 (a : ℚ) (by exact_mod_cast ha.ne_zero)) (Units.mk0 (b : ℚ) (by exact_mod_cast hb.ne_zero)) = 1)
  (hp : Nat.Prime p)
  (hq : Nat.Prime q) :
-- imply
  haveI : Fact (Nat.Prime p) :=
-- proof
  ⟨hp⟩
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    globalHilbertProduct (Units.mk0 (p : ℚ) (by exact_mod_cast hp.ne_zero))
      (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1 := by
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    by_cases hpq : p = q
    · subst hpq; exact h3 p hp
    · by_cases hp2 : p = 2
      · subst hp2
        by_cases hq2 : q = 2
        · subst hq2; exact h3 2 (by decide)
        · exact h4 q hq hq2
      · by_cases hq2 : q = 2
        · subst hq2
          rw [globalHilbertProduct_comm]
          exact h4 p hp hp2
        · exact h5 p q hp hq hp2 hq2 hpq

/--
[globalHilbertProduct_inv_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma globalHilbertProduct_inv_left
  {a b : ℚˣ} :
-- imply
  globalHilbertProduct a⁻¹ b = globalHilbertProduct a b := by
-- proof
  have h := globalHilbertProduct_mul_left a a⁻¹ b
  rw [mul_inv_cancel] at h
  rw [globalHilbertProduct_one_left] at h
  obtain ha | ha <;> := globalHilbertProduct_eq_one_or_neg_one a b
    obtain hai | hai <;> := globalHilbertProduct_eq_one_or_neg_one a⁻¹ b
    simp [ha, hai] at h ⊢ <;> linarith

/--
[globalHilbertProduct_pos_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma globalHilbertProduct_pos_nat
  {b : ℚˣ}
  {n : ℕ}
-- given
  (h2 : ∀ q : ℕ, (hq : Nat.Prime q) → haveI : Fact (Nat.Prime q) := ⟨hq⟩ globalHilbertProduct (-1) (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1)
  (hgen : ∀ q : ℕ, (hq : Nat.Prime q) → haveI : Fact (Nat.Prime q) := ⟨hq⟩ globalHilbertProduct (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) b = 1)
  (hn : n ≠ 0) :
-- imply
  globalHilbertProduct (Units.mk0 (n : ℚ) (by exact_mod_cast hn)) b = 1 := by
-- proof
  induction n using Nat.strongRecOn with
  | _ n ih =>
  by_cases hn1 : n = 1
  · subst hn1
    simp only [Nat.cast_one]
    convert globalHilbertProduct_one_left b using 1
  ·
    have hn_gt : 1 < n := by omega
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    obtain ⟨m, rfl⟩ := hpn
    have hm_pos : m ≠ 0 := by
      intro h; simp [h] at hn
    have hm_lt : m < p * m :=
      lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm_pos) hp.one_lt
    have hcast : (Units.mk0 ((p * m : ℕ) : ℚ) (by exact_mod_cast hn) : ℚ) =
      (Units.mk0 ((p : ℕ) : ℚ) (by exact_mod_cast hp.ne_zero) : ℚ) *
      (Units.mk0 ((m : ℕ) : ℚ) (by exact_mod_cast hm_pos) : ℚ) := by
      simp [Units.val_mk0, Nat.cast_mul]
    have hunit_eq : Units.mk0 ((p * m : ℕ) : ℚ) (by exact_mod_cast hn) =
      Units.mk0 ((p : ℕ) : ℚ) (by exact_mod_cast hp.ne_zero) *
      Units.mk0 ((m : ℕ) : ℚ) (by exact_mod_cast hm_pos) := by
      ext; exact hcast
    rw [hunit_eq, globalHilbertProduct_mul_left]
    rw [hgen p hp, ih m hm_lt hm_pos, mul_one]

/--
[hilbert_product_formula_bilinearity_reduction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbert_product_formula_bilinearity_reduction
  {a b : ℚˣ}
-- given
  (h0 : globalHilbertProduct (-1) (-1) = 1)
  (h1 : ∀ q : ℕ, (hq : Nat.Prime q) → haveI : Fact (Nat.Prime q) := ⟨hq⟩ globalHilbertProduct (-1) (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1)
  (h2 : ∀ q : ℕ, (hq : Nat.Prime q) → haveI : Fact (Nat.Prime q) := ⟨hq⟩ let q' := Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero) globalHilbertProduct q' q' = 1)
  (h3 : ∀ q : ℕ, (hq : Nat.Prime q) → q ≠ 2 → haveI : Fact (Nat.Prime q) := ⟨hq⟩ globalHilbertProduct (Units.mk0 (2 : ℚ) (by norm_num)) (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1)
  (h4 : ∀ a b : ℕ, (ha : Nat.Prime a) → (hb : Nat.Prime b) → a ≠ 2 → b ≠ 2 → a ≠ b → haveI : Fact (Nat.Prime a) := ⟨ha⟩ haveI : Fact (Nat.Prime b) := ⟨hb⟩ globalHilbertProduct (Units.mk0 (a : ℚ) (by exact_mod_cast ha.ne_zero)) (Units.mk0 (b : ℚ) (by exact_mod_cast hb.ne_zero)) = 1) :
-- imply
  globalHilbertProduct a b = 1 := by
-- proof
  have decompose : ∀ (x c : ℚˣ),
    (∀ c' : ℚˣ, globalHilbertProduct (-1) c' = 1) →
    (∀ (n : ℕ) (hn : n ≠ 0) (c' : ℚˣ),
      globalHilbertProduct (Units.mk0 (n : ℚ) (by exact_mod_cast hn)) c' = 1) →
    globalHilbertProduct x c = 1 := by
    intro x c hneg1_any' hnat_any'
    have hnum_ne : (x : ℚ).num ≠ 0 := Rat.num_ne_zero.mpr (Units.ne_zero x)
    have hnatabs_ne : (x : ℚ).num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hnum_ne
    have hden_ne : ((x : ℚ).den : ℚ) ≠ 0 := by exact_mod_cast (x : ℚ).den_pos.ne'
    have hnatabs_cast_ne : ((x : ℚ).num.natAbs : ℚ) ≠ 0 := by exact_mod_cast hnatabs_ne
    have hnum_cast_ne : ((x : ℚ).num : ℚ) ≠ 0 := by exact_mod_cast hnum_ne
    have hx_eq : x = Units.mk0 ((x : ℚ).num : ℚ) hnum_cast_ne *
      (Units.mk0 ((x : ℚ).den : ℚ) hden_ne)⁻¹ := by
      ext
      simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
      have h := Rat.num_div_den (x : ℚ)
      rwa [div_eq_mul_inv] at h
    rw [hx_eq, globalHilbertProduct_mul_left, globalHilbertProduct_inv_left]
    have hden_eq : globalHilbertProduct (Units.mk0 ((x : ℚ).den : ℚ) hden_ne) c = 1 :=
      hnat_any' (x : ℚ).den (x : ℚ).den_pos.ne' c
    rw [hden_eq, mul_one]
    by_cases hpos : 0 < (x : ℚ).num
    ·
      have hcast_eq : Units.mk0 ((x : ℚ).num : ℚ) hnum_cast_ne =
        Units.mk0 ((x : ℚ).num.natAbs : ℚ) hnatabs_cast_ne := by
        ext; simp [Units.val_mk0]
        have : (x : ℚ).num = ((x : ℚ).num.natAbs : ℤ) := by omega
        exact_mod_cast this
      rw [hcast_eq]
      exact hnat_any' _ hnatabs_ne c
    ·
      have hnum_neg : (x : ℚ).num < 0 := by omega
      have hcast_eq : Units.mk0 ((x : ℚ).num : ℚ) hnum_cast_ne =
        (-1 : ℚˣ) * Units.mk0 ((x : ℚ).num.natAbs : ℚ) hnatabs_cast_ne := by
        ext; simp [Units.val_mk0]
        have : (x : ℚ).num = -((x : ℚ).num.natAbs : ℤ) := by omega
        exact_mod_cast this
      rw [hcast_eq, globalHilbertProduct_mul_left, hneg1_any', hnat_any' _ hnatabs_ne, one_mul]
  suffices hprime_any : ∀ (p : ℕ) (hp : Nat.Prime p),
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    ∀ (c : ℚˣ), globalHilbertProduct (Units.mk0 (p : ℚ) (by exact_mod_cast hp.ne_zero)) c = 1 by
    suffices hneg1_any : ∀ c : ℚˣ, globalHilbertProduct (-1) c = 1 by
      suffices hnat_any : ∀ (n : ℕ) (hn : n ≠ 0) (c : ℚˣ),
        globalHilbertProduct (Units.mk0 (n : ℚ) (by exact_mod_cast hn)) c = 1 by
        exact decompose a b hneg1_any hnat_any
      intro n hn c
      exact globalHilbertProduct_pos_nat c h2 (fun q hq => hprime_any q hq c) n hn
    intro c
    rw [globalHilbertProduct_comm]
    have hnum_ne : (c : ℚ).num ≠ 0 := Rat.num_ne_zero.mpr (Units.ne_zero c)
    have hnatabs_ne : (c : ℚ).num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hnum_ne
    have hden_ne : ((c : ℚ).den : ℚ) ≠ 0 := by exact_mod_cast (c : ℚ).den_pos.ne'
    have hnatabs_cast_ne : ((c : ℚ).num.natAbs : ℚ) ≠ 0 := by exact_mod_cast hnatabs_ne
    have hnum_cast_ne : ((c : ℚ).num : ℚ) ≠ 0 := by exact_mod_cast hnum_ne
    have hc_eq : c = Units.mk0 ((c : ℚ).num : ℚ) hnum_cast_ne *
      (Units.mk0 ((c : ℚ).den : ℚ) hden_ne)⁻¹ := by
      ext
      simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
      have h := Rat.num_div_den (c : ℚ)
      rw [div_eq_mul_inv] at h; exact h.symm
    rw [hc_eq, globalHilbertProduct_mul_left, globalHilbertProduct_inv_left]
    have hnat_neg1 : ∀ (n : ℕ) (hn : n ≠ 0),
      globalHilbertProduct (Units.mk0 (n : ℚ) (by exact_mod_cast hn)) (-1) = 1 := by
      intro n hn
      rw [globalHilbertProduct_comm]
      induction n using Nat.strongRecOn with
      | _ n ih =>
      by_cases hn1 : n = 1
      · subst hn1; simp only [Nat.cast_one]
        have hmk : Units.mk0 (1 : ℚ) (by norm_num) = (1 : ℚˣ) := by ext; simp
        rw [hmk, globalHilbertProduct_comm]
        exact globalHilbertProduct_one_left _
      · have hn_gt : 1 < n := by omega
        obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
        obtain ⟨m, rfl⟩ := hpn
        have hm_pos : m ≠ 0 := by intro h; simp [h] at hn
        have hm_lt : m < p * m :=
          lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm_pos) hp.one_lt
        have hunit_eq : Units.mk0 ((p * m : ℕ) : ℚ) (by exact_mod_cast hn) =
          Units.mk0 ((p : ℕ) : ℚ) (by exact_mod_cast hp.ne_zero) *
          Units.mk0 ((m : ℕ) : ℚ) (by exact_mod_cast hm_pos) := by
          ext; simp [Units.val_mk0, Nat.cast_mul]
        rw [hunit_eq, globalHilbertProduct_mul_right]
        haveI : Fact (Nat.Prime p) := ⟨hp⟩
        rw [h2 p hp, ih m hm_lt hm_pos, mul_one]
    have hden_one : globalHilbertProduct (Units.mk0 ((c : ℚ).den : ℚ) hden_ne) (-1) = 1 :=
      hnat_neg1 _ (c : ℚ).den_pos.ne'
    rw [hden_one, mul_one]
    by_cases hpos : 0 < (c : ℚ).num
    · have hcast_eq : Units.mk0 ((c : ℚ).num : ℚ) hnum_cast_ne =
      Units.mk0 ((c : ℚ).num.natAbs : ℚ) hnatabs_cast_ne := by
      ext; simp [Units.val_mk0]
      have : (c : ℚ).num = ((c : ℚ).num.natAbs : ℤ) := by omega
      exact_mod_cast this
      rw [hcast_eq]; exact hnat_neg1 _ hnatabs_ne
    · have hnum_neg : (c : ℚ).num < 0 := by omega
      have hcast_eq : Units.mk0 ((c : ℚ).num : ℚ) hnum_cast_ne =
        (-1 : ℚˣ) * Units.mk0 ((c : ℚ).num.natAbs : ℚ) hnatabs_cast_ne := by
        ext; simp [Units.val_mk0]
        have : (c : ℚ).num = -((c : ℚ).num.natAbs : ℤ) := by omega
        exact_mod_cast this
      rw [hcast_eq, globalHilbertProduct_mul_left, h1, hnat_neg1 _ hnatabs_ne, one_mul]
  intro p hp
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  intro c
  rw [globalHilbertProduct_comm]
  have hnat_p : ∀ (n : ℕ) (hn : n ≠ 0),
    globalHilbertProduct (Units.mk0 (n : ℚ) (by exact_mod_cast hn))
      (Units.mk0 (p : ℚ) (by exact_mod_cast hp.ne_zero)) = 1 := by
    intro n hn
    exact globalHilbertProduct_pos_nat
      (Units.mk0 (p : ℚ) (by exact_mod_cast hp.ne_zero))
      h2
      (fun q hq => globalHilbertProduct_generators h1 h2 h3 h4 h5 q p hq hp)
      n hn
  have hnum_ne : (c : ℚ).num ≠ 0 := Rat.num_ne_zero.mpr (Units.ne_zero c)
  have hnatabs_ne : (c : ℚ).num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hnum_ne
  have hden_ne : ((c : ℚ).den : ℚ) ≠ 0 := by exact_mod_cast (c : ℚ).den_pos.ne'
  have hnatabs_cast_ne : ((c : ℚ).num.natAbs : ℚ) ≠ 0 := by exact_mod_cast hnatabs_ne
  have hnum_cast_ne : ((c : ℚ).num : ℚ) ≠ 0 := by exact_mod_cast hnum_ne
  have hc_eq : c = Units.mk0 ((c : ℚ).num : ℚ) hnum_cast_ne *
    (Units.mk0 ((c : ℚ).den : ℚ) hden_ne)⁻¹ := by
    ext
    simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
    have h := Rat.num_div_den (c : ℚ)
    rw [div_eq_mul_inv] at h; exact h.symm
  rw [hc_eq, globalHilbertProduct_mul_left, globalHilbertProduct_inv_left]
  have hden_one : globalHilbertProduct (Units.mk0 ((c : ℚ).den : ℚ) hden_ne)
    (Units.mk0 (p : ℚ) (by exact_mod_cast hp.ne_zero)) = 1 :=
    hnat_p _ (c : ℚ).den_pos.ne'
  rw [hden_one, mul_one]
  by_cases hpos : 0 < (c : ℚ).num
  · have hcast_eq : Units.mk0 ((c : ℚ).num : ℚ) hnum_cast_ne =
    Units.mk0 ((c : ℚ).num.natAbs : ℚ) hnatabs_cast_ne := by
    ext; simp [Units.val_mk0]
    have : (c : ℚ).num = ((c : ℚ).num.natAbs : ℤ) := by omega
    exact_mod_cast this
    rw [hcast_eq]; exact hnat_p _ hnatabs_ne
  · have hnum_neg : (c : ℚ).num < 0 := by omega
    have hcast_eq : Units.mk0 ((c : ℚ).num : ℚ) hnum_cast_ne =
      (-1 : ℚˣ) * Units.mk0 ((c : ℚ).num.natAbs : ℚ) hnatabs_cast_ne := by
      ext; simp [Units.val_mk0]
      have : (c : ℚ).num = -((c : ℚ).num.natAbs : ℤ) := by omega
      exact_mod_cast this
    rw [hcast_eq, globalHilbertProduct_mul_left, h2 p hp, hnat_p _ hnatabs_ne, one_mul]

/--
[hilbert_product_neg_one_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbert_product_neg_one_prime
  {q : ℕ}
-- given
  (hq : Nat.Prime q) :
-- imply
  haveI : Fact (Nat.Prime q) :=
-- proof
  ⟨hq⟩
    globalHilbertProduct (-1) (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1 := by
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    by_cases hq2 : q = 2
    ·
      subst hq2
      let b : ℚˣ := Units.mk0 (2 : ℚ) (by norm_num)
      show globalHilbertProduct (-1) b = 1
      unfold globalHilbertProduct
      have h_infty : hilbertAtInfty (-1) b = 1 := by
        unfold hilbertAtInfty realHilbertSymbol
        rw [hilbertSymbol.eq_one_iff]
        refine ⟨1, 1, ?_⟩
        simp only [ratToRealUnits_val, Units.val_neg, Units.val_one, Rat.cast_neg, Rat.cast_one,
          Units.val_mk0, Rat.cast_ofNat, one_pow, mul_one, b]
        norm_num
      have h_prime : ∀ (p : Nat.Primes),
        (haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
          hilbertAtPrime p.val (-1) b) = 1 := by
        intro ⟨p_val, hp_prime⟩
        haveI : Fact (Nat.Prime p_val) := ⟨hp_prime⟩
        show hilbertAtPrime p_val (-1) b = 1
        unfold hilbertAtPrime padicHilbertSymbol
        rw [hilbertSymbol.eq_one_iff]
        refine ⟨1, 1, ?_⟩
        simp only [ratToQpUnits_val, Units.val_neg, Units.val_one, Rat.cast_neg, Rat.cast_one,
          Units.val_mk0, Rat.cast_ofNat, one_pow, mul_one, b]
        norm_num
      rw [h_infty]
      simp only [one_mul]
      rw [show (fun (p : Nat.Primes) => haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩;
        hilbertAtPrime p.val (-1) b) = fun _ => (1 : ℤ) from funext h_prime]
      simp [finprod_one]
    ·
      exact hilbert_product_neg_one_odd_prime_aux q hq hq2

/--
[hilbert_product_prime_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbert_product_prime_self
  {q : ℕ}
-- given
  (hq : Nat.Prime q) :
-- imply
  haveI : Fact (Nat.Prime q) :=
-- proof
  ⟨hq⟩
    let q' := Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)
    globalHilbertProduct q' q' = 1 := by
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    intro q'
    suffices h : globalHilbertProduct q' q' = globalHilbertProduct (-1) q' by
      rw [h]
      exact hilbert_product_neg_one_prime q hq
    unfold globalHilbertProduct
    congr 1
    ·
      unfold hilbertAtInfty
      show realHilbertSymbol (ratToRealUnits q') (ratToRealUnits q') =
        realHilbertSymbol (ratToRealUnits (-1)) (ratToRealUnits q')
      rw [show realHilbertSymbol (ratToRealUnits q') (ratToRealUnits q') =
        realHilbertSymbol (-1) (ratToRealUnits q') from by
        unfold realHilbertSymbol; exact hilbertSymbol.hilbert_self_eq_neg_one _]
      congr 1
      ext; simp [ratToRealUnits]
    ·
      apply finprod_congr
      intro ⟨p_val, hp_prime⟩
      haveI : Fact (Nat.Prime p_val) := ⟨hp_prime⟩
      show hilbertAtPrime p_val q' q' = hilbertAtPrime p_val (-1) q'
      unfold hilbertAtPrime
      show padicHilbertSymbol p_val (ratToQpUnits p_val q') (ratToQpUnits p_val q') =
        padicHilbertSymbol p_val (ratToQpUnits p_val (-1)) (ratToQpUnits p_val q')
      rw [show padicHilbertSymbol p_val (ratToQpUnits p_val q') (ratToQpUnits p_val q') =
        padicHilbertSymbol p_val (-1) (ratToQpUnits p_val q') from by
        unfold padicHilbertSymbol; exact hilbertSymbol.hilbert_self_eq_neg_one _]
      congr 1
      ext; simp [ratToQpUnits]

/--
[hilbertAtPrime_two_q_eq_one_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbertAtPrime_two_q_eq_one_of_ne
  {q : ℕ}
  {p : ℕ}
  [Fact (Nat.Prime p)]
-- given
  (hq : Nat.Prime q)
  (hq_odd : q ≠ 2)
  (hp2 : p ≠ 2)
  (hpq : p ≠ q) :
-- imply
  hilbertAtPrime p (Units.mk0 (2 : ℚ) (by norm_num)) (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1 := by
-- proof
  unfold hilbertAtPrime
  obtain ⟨u, hu⟩ := ratToQpUnits_two_at_odd_prime p hp2
  have hpq_dvd : ¬ (p ∣ q) := by
    intro h
    have := hq.eq_one_or_self_of_dvd p h
    obtain h1 | h1 := this
    · exact (Fact.out : Nat.Prime p).one_lt.ne' h1
    · exact absurd h1 hpq
  obtain ⟨v, hv⟩ := ratToQpUnits_eq_unitZpToQp_of_not_dvd p
    (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero))
    (by simp only [Units.val_mk0, Rat.num_natCast, Int.natAbs_natCast]; exact hpq_dvd)
    (by simp only [Units.val_mk0, Rat.den_natCast]
      exact Nat.Prime.not_dvd_one (Fact.out : Nat.Prime p))
  rw [hu, hv]
  exact hilbert_symbol_units_eq_one_of_odd p hp2 u v

/--
[hilbertAtInfty_two_q](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbertAtInfty_two_q
  {q : ℕ}
-- given
  (hq : Nat.Prime q) :
-- imply
  hilbertAtInfty (Units.mk0 (2 : ℚ) (by norm_num)) (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1 := by
-- proof
  unfold hilbertAtInfty
  rw [realHilbertSymbol.eq_one_iff]
  exact realHilbertSymbol.isSolvable_of_pos_left (by simp [ratToRealUnits])

/--
[hilbertAtPrime_two_q_at_q](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbertAtPrime_two_q_at_q
  {q : ℕ}
-- given
  (hq : Nat.Prime q)
  (hq_odd : q ≠ 2) :
-- imply
  haveI : Fact (Nat.Prime q) :=
-- proof
  ⟨hq⟩
    ∀ u : ℤ_[q]ˣ, ratToQpUnits q (Units.mk0 (2 : ℚ) (by norm_num)) = unitZpToQp u →
    hilbertAtPrime q (Units.mk0 (2 : ℚ) (by norm_num))
      (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = padicUnitLegendre u := by
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    intro u hu
    unfold hilbertAtPrime
    rw [hu, ratToQpUnits_natPrime_eq_qpPrime q]
    show padicHilbertSymbol q (unitZpToQp u) (qpPrime q) = padicUnitLegendre u
    rw [show padicHilbertSymbol q (unitZpToQp u) (qpPrime q) =
      padicHilbertSymbol q (qpPrime q) (unitZpToQp u) from
      hilbertSymbol.symm (unitZpToQp u) (qpPrime q)]
    exact hilbert_p_unit_eq_legendre hq_odd u

/--
[hilbertAtPrime_two_q_at_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbertAtPrime_two_q_at_two
  {q : ℕ}
-- given
  (hq : Nat.Prime q)
  (hq_odd : q ≠ 2) :
-- imply
  ∀ v : ℤ_[2]ˣ, ratToQpUnits 2 (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = unitZpToQp v → hilbertAtPrime 2 (Units.mk0 (2 : ℚ) (by norm_num)) (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = hilbert2Adic_formula (toZModPow_unit 3 (1 : ℤ_[2]ˣ)) (toZModPow_unit 3 v) 1 0 := by
-- proof
  intro v hv
  unfold hilbertAtPrime
  rw [ratToQpUnits_two_eq_twoQp, twoQp_eq_padicUnit_two_one]
  have hv_unit : ratToQpUnits 2 (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) =
    padicUnit_one v := by
    rw [hv]
    ext
    simp [unitZpToQp_coe, padicUnit_one_val]
  rw [hv_unit]
  exact thm_10_9_two_one 1 v

/--
[padicUnitLegendre_times_hilbert2Adic_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma padicUnitLegendre_times_hilbert2Adic_eq_one
  {q : ℕ}
-- given
  (hq : Nat.Prime q)
  (hq_odd : q ≠ 2) :
-- imply
  haveI : Fact (Nat.Prime q) :=
-- proof
  ⟨hq⟩
    ∀ (u : ℤ_[q]ˣ) (hu : ratToQpUnits q (Units.mk0 (2 : ℚ) (by norm_num)) = unitZpToQp u)
    (v : ℤ_[2]ˣ) (hv : ratToQpUnits 2 (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = unitZpToQp v),
    padicUnitLegendre u *
    hilbert2Adic_formula (toZModPow_unit 3 (1 : ℤ_[2]ˣ)) (toZModPow_unit 3 v) 1 0 = 1 := by
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    intro u hu v hv
    have hleg_u : padicUnitLegendre u = legendreSym q 2 := by
      have h_Qp_eq : ((u : ℤ_[q]) : ℚ_[q]) = ((2 : ℚ) : ℚ_[q]) := by
        have := congr_arg Units.val hu.symm
        rwa [unitZpToQp_coe, ratToQpUnits_val] at this
      have h_toZMod : PadicInt.toZMod (u : ℤ_[q]) = (2 : ZMod q) := by
        have h_coe_eq : (u : ℤ_[q]) = ((2 : ℤ) : ℤ_[q]) := by
          apply Subtype.coe_injective
          show ((u : ℤ_[q]) : ℚ_[q]) = (((2 : ℤ) : ℤ_[q]) : ℚ_[q])
          rw [h_Qp_eq]; norm_cast
        rw [h_coe_eq]
        exact_mod_cast map_intCast PadicInt.toZMod 2
      unfold padicUnitLegendre legendreSym
      congr 1
      haveI : NeZero (q : ℕ) := ⟨(Fact.out : Nat.Prime q).ne_zero⟩
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id', id, h_toZMod]
    have hleg_v : hilbert2Adic_formula (toZModPow_unit 3 1) (toZModPow_unit 3 v) 1 0 =
      legendreSym q 2 := by
      rw [toZModPow_unit_one]
      have h_formula_eq_chi8 : ∀ v₀ : (ZMod (2 ^ 3))ˣ,
        hilbert2Adic_formula 1 v₀ 1 0 = ZMod.χ₈ (↑v₀) := by native_decide
      rw [h_formula_eq_chi8]
      have h_v_eq_q : (toZModPow_unit 3 v : ZMod (2 ^ 3)) = ((q : ℤ) : ZMod (2 ^ 3)) := by
        rw [toZModPow_unit_coe]
        have h_Qp_eq : ((v : ℤ_[2]) : ℚ_[2]) = ((q : ℚ) : ℚ_[2]) := by
          have := congr_arg Units.val hv.symm
          rwa [unitZpToQp_coe, ratToQpUnits_val] at this
        have h_coe_eq : (v : ℤ_[2]) = ((q : ℤ) : ℤ_[2]) := by
          apply Subtype.coe_injective
          show ((v : ℤ_[2]) : ℚ_[2]) = (((q : ℤ) : ℤ_[2]) : ℚ_[2])
          rw [h_Qp_eq]; push_cast; ring
        rw [h_coe_eq]
        exact map_intCast (PadicInt.toZModPow 3) q
      rw [show (↑(toZModPow_unit 3 v) : ZMod (2^3)) = ((q : ℤ) : ZMod (2^3)) from h_v_eq_q]
      rw [legendreSym.at_two hq_odd]
      push_cast
      rfl
    rw [hleg_u, hleg_v]
    have hval := quadraticChar_isQuadratic (F := ZMod q) ((2 : ℤ) : ZMod q)
    unfold legendreSym
    obtain h | h | h := hval
    · exfalso
      rw [quadraticChar_eq_zero_iff] at h
      have h2 : ((q : ℤ) ∣ 2) := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 q).mp h
      have hq_ge : (q : ℤ) ≥ 3 := by
        have := hq.two_le
        omega
      linarith [Int.le_of_dvd (by norm_num : (0 : ℤ) < 2) h2]
    · rw [h]; norm_num
    · rw [h]; norm_num

/--
[hilbertAtPrime_two_q_product](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbertAtPrime_two_q_product
  {q : ℕ}
-- given
  (hq : Nat.Prime q)
  (hq_odd : q ≠ 2) :
-- imply
  haveI : Fact (Nat.Prime q) :=
-- proof
  ⟨hq⟩
    hilbertAtPrime q (Units.mk0 (2 : ℚ) (by norm_num))
      (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) *
    hilbertAtPrime 2 (Units.mk0 (2 : ℚ) (by norm_num))
      (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1 := by
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    obtain ⟨u, hu⟩ := ratToQpUnits_two_at_odd_prime q hq_odd
    obtain ⟨v, hv⟩ := ratToQpUnits_prime_at_two q hq hq_odd
    rw [hilbertAtPrime_two_q_at_q q hq hq_odd u hu]
    rw [hilbertAtPrime_two_q_at_two q hq hq_odd v hv]
    exact padicUnitLegendre_times_hilbert2Adic_eq_one q hq hq_odd u hu v hv

/--
[hilbert_product_two_odd_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbert_product_two_odd_prime
  {q : ℕ}
-- given
  (hq : Nat.Prime q)
  (hq_odd : q ≠ 2) :
-- imply
  haveI : Fact (Nat.Prime q) :=
-- proof
  ⟨hq⟩
    globalHilbertProduct (Units.mk0 (2 : ℚ) (by norm_num))
      (Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)) = 1 := by
    haveI : Fact (Nat.Prime q) := ⟨hq⟩
    unfold globalHilbertProduct
    let a : ℚˣ := Units.mk0 (2 : ℚ) (by norm_num)
    let b : ℚˣ := Units.mk0 (q : ℚ) (by exact_mod_cast hq.ne_zero)
    let f : Nat.Primes → ℤ := fun p =>
      haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
      hilbertAtPrime p.val a b
    suffices h : hilbertAtInfty a b * ∏ᶠ (p : Nat.Primes), f p = 1 by
      convert h
    have h2 : Nat.Prime 2 := by decide
    let two : Nat.Primes := ⟨2, h2⟩
    let q_prime : Nat.Primes := ⟨q, hq⟩
    have hneq : two ≠ q_prime := by
      intro h
      have : (2 : ℕ) = q := congr_arg Subtype.val h
      exact hq_odd this.symm
    have hsupp : Function.mulSupport f ⊆ ↑({two, q_prime} : Finset Nat.Primes) := by
      intro p hp
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      rw [Function.mem_mulSupport] at hp
      by_contra hne
      push_neg at hne
      apply hp
      have hp2 : p.val ≠ 2 := by
        intro h; exact hne.1 (Subtype.ext h)
      have hpq : p.val ≠ q := by
        intro h; exact hne.2 (Subtype.ext h)
      haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
      exact hilbertAtPrime_two_q_eq_one_of_ne q hq hq_odd p.val hp2 hpq
    rw [finprod_eq_prod_of_mulSupport_subset f hsupp]
    simp only [Finset.prod_pair hneq]
    show hilbertAtInfty a b * (f two * f q_prime) = 1
    simp only [f, two, q_prime]
    rw [hilbertAtInfty_two_q q hq]
    simp only [one_mul]
    rw [mul_comm]
    exact hilbertAtPrime_two_q_product q hq hq_odd

/--
[hilbert_qr_cancellation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbert_qr_cancellation
  {a b : ℕ}
  [instA : Fact (Nat.Prime a)]
  [instB : Fact (Nat.Prime b)]
  {u_a2 : ℤ_[2]ˣ}
  {u_b2 : ℤ_[2]ˣ}
  {ub_a : ℤ_[a]ˣ}
  {ua_b : ℤ_[b]ˣ}
-- given
  (ha : Nat.Prime a)
  (hb : Nat.Prime b)
  (ha_odd : a ≠ 2)
  (hb_odd : b ≠ 2)
  (hab : a ≠ b)
  (hu_a2 : ratToQpUnits 2 (Units.mk0 (↑a : ℚ) (by exact_mod_cast ha.ne_zero)) = unitZpToQp u_a2)
  (hu_b2 : ratToQpUnits 2 (Units.mk0 (↑b : ℚ) (by exact_mod_cast hb.ne_zero)) = unitZpToQp u_b2)
  (hub_a : ratToQpUnits a (Units.mk0 (↑b : ℚ) (by exact_mod_cast hb.ne_zero)) = unitZpToQp ub_a)
  (hua_b : ratToQpUnits b (Units.mk0 (↑a : ℚ) (by exact_mod_cast ha.ne_zero)) = unitZpToQp ua_b) :
-- imply
  hilbert2Adic_formula (toZModPow_unit 3 u_a2) (toZModPow_unit 3 u_b2) 0 0 * padicUnitLegendre ub_a * padicUnitLegendre ua_b = 1 := by
-- proof
  have hub_val : (ub_a : ℤ_[a]) = (b : ℤ_[a]) := by
    have h1 : (unitZpToQp ub_a : ℚ_[a]) = ((ub_a : ℤ_[a]) : ℚ_[a]) := unitZpToQp_coe ub_a
    have h2 : (ratToQpUnits a (Units.mk0 (↑b : ℚ) (by exact_mod_cast hb.ne_zero)) : ℚ_[a]) =
      ((b : ℚ) : ℚ_[a]) := ratToQpUnits_val a _
    have h3 : ((ub_a : ℤ_[a]) : ℚ_[a]) = ((b : ℤ_[a]) : ℚ_[a]) := by
      rw [← h1, ← hub_a, h2]; push_cast; ring
    exact Subtype.val_injective h3
  have hua_val : (ua_b : ℤ_[b]) = (a : ℤ_[b]) := by
    have h1 : (unitZpToQp ua_b : ℚ_[b]) = ((ua_b : ℤ_[b]) : ℚ_[b]) := unitZpToQp_coe ua_b
    have h2 : (ratToQpUnits b (Units.mk0 (↑a : ℚ) (by exact_mod_cast ha.ne_zero)) : ℚ_[b]) =
      ((a : ℚ) : ℚ_[b]) := ratToQpUnits_val b _
    have h3 : ((ua_b : ℤ_[b]) : ℚ_[b]) = ((a : ℤ_[b]) : ℚ_[b]) := by
      rw [← h1, ← hua_b, h2]; push_cast; ring
    exact Subtype.val_injective h3
  have hu_a2_val : (u_a2 : ℤ_[2]) = (a : ℤ_[2]) := by
    have h1 : (unitZpToQp u_a2 : ℚ_[2]) = ((u_a2 : ℤ_[2]) : ℚ_[2]) := unitZpToQp_coe u_a2
    have h2 : (ratToQpUnits 2 (Units.mk0 (↑a : ℚ) (by exact_mod_cast ha.ne_zero)) : ℚ_[2]) =
      ((a : ℚ) : ℚ_[2]) := ratToQpUnits_val 2 _
    have h3 : ((u_a2 : ℤ_[2]) : ℚ_[2]) = ((a : ℤ_[2]) : ℚ_[2]) := by
      rw [← h1, ← hu_a2, h2]; push_cast; ring
    exact Subtype.val_injective h3
  have hu_b2_val : (u_b2 : ℤ_[2]) = (b : ℤ_[2]) := by
    have h1 : (unitZpToQp u_b2 : ℚ_[2]) = ((u_b2 : ℤ_[2]) : ℚ_[2]) := unitZpToQp_coe u_b2
    have h2 : (ratToQpUnits 2 (Units.mk0 (↑b : ℚ) (by exact_mod_cast hb.ne_zero)) : ℚ_[2]) =
      ((b : ℚ) : ℚ_[2]) := ratToQpUnits_val 2 _
    have h3 : ((u_b2 : ℤ_[2]) : ℚ_[2]) = ((b : ℤ_[2]) : ℚ_[2]) := by
      rw [← h1, ← hu_b2, h2]; push_cast; ring
    exact Subtype.val_injective h3
  have hleg_ba : padicUnitLegendre ub_a = legendreSym a (b : ℤ) := by
    unfold padicUnitLegendre
    rw [hub_val, map_natCast, ZMod.val_natCast]
    simp only [legendreSym]
    congr 1
    exact_mod_cast (ZMod.natCast_mod b a ▸ rfl : ((b % a : ℕ) : ZMod a) = ((b : ℕ) : ZMod a))
  have hleg_ab : padicUnitLegendre ua_b = legendreSym b (a : ℤ) := by
    unfold padicUnitLegendre
    rw [hua_val, map_natCast, ZMod.val_natCast]
    simp only [legendreSym]
    congr 1
    exact_mod_cast (ZMod.natCast_mod a b ▸ rfl : ((a % b : ℕ) : ZMod b) = ((a : ℕ) : ZMod b))
  rw [hleg_ba, hleg_ab]
  have hqr := legendreSym.quadratic_reciprocity ha_odd hb_odd hab
  have hleg_prod : legendreSym a (↑b) * legendreSym b (↑a) = (-1) ^ (a / 2 * (b / 2)) := by
    rw [mul_comm]; exact hqr
  rw [mul_assoc, hleg_prod]
  unfold hilbert2Adic_formula
  simp only [Nat.cast_zero, zero_mul, add_zero]
  have hcoe_a : (toZModPow_unit 3 u_a2 : ZMod (2^3)) = (a : ZMod (2^3)) := by
    rw [toZModPow_unit_coe, hu_a2_val, map_natCast]
  have hcoe_b : (toZModPow_unit 3 u_b2 : ZMod (2^3)) = (b : ZMod (2^3)) := by
    rw [toZModPow_unit_coe, hu_b2_val, map_natCast]
  have hval_a : (toZModPow_unit 3 u_a2 : ZMod (2^3)).val = a % (2^3) := by
    rw [hcoe_a]; exact ZMod.val_natCast (n := 2^3) a
  have hval_b : (toZModPow_unit 3 u_b2 : ZMod (2^3)).val = b % (2^3) := by
    rw [hcoe_b]; exact ZMod.val_natCast (n := 2^3) b
  simp only [epsilon_ZMod8, hval_a, hval_b]
  have ha2_odd : a % 2 = 1 := by
    obtain rfl | h := ha.eq_two_or_odd
    · exact absurd rfl ha_odd
    · exact h
  have hb2_odd : b % 2 = 1 := by
    obtain rfl | h := hb.eq_two_or_odd
    · exact absurd rfl hb_odd
    · exact h
  have ha2 : ((((a % 2 ^ 3 - 1) / 2 : ℕ) : ZMod 2)) = ((a / 2 : ℕ) : ZMod 2) := by
    rw [ZMod.natCast_eq_natCast_iff']; omega
  have hb2 : ((((b % 2 ^ 3 - 1) / 2 : ℕ) : ZMod 2)) = ((b / 2 : ℕ) : ZMod 2) := by
    rw [ZMod.natCast_eq_natCast_iff']; omega
  rw [ha2, hb2, ← Nat.cast_mul, ZMod.val_natCast (n := 2)]
  set n := a / 2 * (b / 2)
  have : (-1 : ℤ) ^ n = (-1 : ℤ) ^ (n % 2) := by
    conv_lhs => rw [show n = 2 * (n / 2) + n % 2 from (Nat.div_add_mod n 2).symm]
    simp [pow_add, pow_mul]
  rw [this, ← pow_add]
  simp

/--
[hilbert_product_distinct_odd_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbert_product_distinct_odd_primes
  {a b : ℕ}
-- given
  (ha : Nat.Prime a)
  (hb : Nat.Prime b)
  (ha_odd : a ≠ 2)
  (hb_odd : b ≠ 2)
  (hab : a ≠ b) :
-- imply
  haveI : Fact (Nat.Prime a) :=
-- proof
  ⟨ha⟩
    haveI : Fact (Nat.Prime b) := ⟨hb⟩
    globalHilbertProduct (Units.mk0 (a : ℚ) (by exact_mod_cast ha.ne_zero))
      (Units.mk0 (b : ℚ) (by exact_mod_cast hb.ne_zero)) = 1 := by
    haveI instA : Fact (Nat.Prime a) := ⟨ha⟩
    haveI instB : Fact (Nat.Prime b) := ⟨hb⟩
    let a' := Units.mk0 (a : ℚ) (by exact_mod_cast ha.ne_zero)
    let b' := Units.mk0 (b : ℚ) (by exact_mod_cast hb.ne_zero)
    unfold globalHilbertProduct
    let f : Nat.Primes → ℤ := fun p =>
      haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
      hilbertAtPrime p.val a' b'
    suffices h : hilbertAtInfty a' b' * ∏ᶠ (p : Nat.Primes), f p = 1 by
      convert h
    have h2 : Nat.Prime 2 := by decide
    let two : Nat.Primes := ⟨2, h2⟩
    let pa : Nat.Primes := ⟨a, ha⟩
    let pb : Nat.Primes := ⟨b, hb⟩
    have hpa_ne_two : pa ≠ two := by intro h; exact ha_odd (Subtype.ext_iff.mp h)
    have hpb_ne_two : pb ≠ two := by intro h; exact hb_odd (Subtype.ext_iff.mp h)
    have hpa_ne_pb : pa ≠ pb := by intro h; exact hab (Subtype.ext_iff.mp h)
    have hsupp : Function.mulSupport f ⊆ ↑({two, pa, pb} : Finset Nat.Primes) := by
      intro p hp
      simp only [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      rw [Function.mem_mulSupport] at hp
      by_contra hne
      push Not at hne
      obtain ⟨hne2, hnea, hneb⟩ := hne
      apply hp
      haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
      have hp2 : p.val ≠ 2 := by intro h; exact hne2 (Subtype.ext h)
      have hna : ¬ (p.val ∣ a) := by
        intro h
        have := ha.eq_one_or_self_of_dvd p.val h
        obtain h1 | h1 := this
        · exact p.property.one_lt.ne' h1
        · exact hnea (Subtype.ext h1)
      have hnb : ¬ (p.val ∣ b) := by
        intro h
        have := hb.eq_one_or_self_of_dvd p.val h
        obtain h1 | h1 := this
        · exact p.property.one_lt.ne' h1
        · exact hneb (Subtype.ext h1)
      have hnum_a : ¬ (p.val ∣ (a' : ℚ).num.natAbs) := by
        simp only [a', Units.val_mk0, Rat.num_natCast, Int.natAbs_natCast]; exact hna
      have hden_a : ¬ (p.val ∣ (a' : ℚ).den) := by
        simp only [a', Units.val_mk0, Rat.den_natCast]
        exact fun h => p.property.one_lt.ne' (Nat.eq_one_of_dvd_one h)
      have hnum_b : ¬ (p.val ∣ (b' : ℚ).num.natAbs) := by
        simp only [b', Units.val_mk0, Rat.num_natCast, Int.natAbs_natCast]; exact hnb
      have hden_b : ¬ (p.val ∣ (b' : ℚ).den) := by
        simp only [b', Units.val_mk0, Rat.den_natCast]
        exact fun h => p.property.one_lt.ne' (Nat.eq_one_of_dvd_one h)
      obtain ⟨ua, hua⟩ := ratToQpUnits_eq_unitZpToQp_of_not_dvd p.val a' hnum_a hden_a
      obtain ⟨ub, hub⟩ := ratToQpUnits_eq_unitZpToQp_of_not_dvd p.val b' hnum_b hden_b
      show f p = 1
      simp only [f]
      unfold hilbertAtPrime
      rw [hua, hub]
      exact hilbert_symbol_units_eq_one_of_odd p.val hp2 ua ub
    rw [finprod_eq_prod_of_mulSupport_subset f hsupp]
    have hprod : ({two, pa, pb} : Finset Nat.Primes).prod f = f two * f pa * f pb := by
      have h1 : pb ∉ ({two, pa} : Finset Nat.Primes) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not; exact ⟨fun h => hb_odd (Subtype.ext_iff.mp h), fun h => hab (Subtype.ext_iff.mp h).symm⟩
      have h2 : pa ∉ ({two} : Finset Nat.Primes) := by
        simp only [Finset.mem_singleton]
        exact fun h => ha_odd (Subtype.ext_iff.mp h)
      rw [show ({two, pa, pb} : Finset Nat.Primes) = insert pb {two, pa} from by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
      rw [Finset.prod_insert h1]
      rw [show ({two, pa} : Finset Nat.Primes) = insert pa {two} from by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
      rw [Finset.prod_insert h2, Finset.prod_singleton]
      ring
    rw [hprod]
    have hinfty : hilbertAtInfty a' b' = 1 := by
      unfold hilbertAtInfty
      rw [realHilbertSymbol.eq_one_iff]
      exact realHilbertSymbol.isSolvable_of_pos_left (by
        simp only [a', ratToRealUnits_val, Units.val_mk0]
        exact_mod_cast ha.pos)
    obtain ⟨u_a2, hu_a2⟩ := ratToQpUnits_prime_at_two a ha ha_odd
    obtain ⟨u_b2, hu_b2⟩ := ratToQpUnits_prime_at_two b hb hb_odd
    have hf_two : f two = hilbert2Adic_formula (toZModPow_unit 3 u_a2) (toZModPow_unit 3 u_b2) 0 0 := by
      simp only [f, two]
      unfold hilbertAtPrime
      have ha2_eq : ratToQpUnits 2 a' = padicUnit_one u_a2 := by
        rw [hu_a2]; ext; simp [unitZpToQp_coe, padicUnit_one_val]
      have hb2_eq : ratToQpUnits 2 b' = padicUnit_one u_b2 := by
        rw [hu_b2]; ext; simp [unitZpToQp_coe, padicUnit_one_val]
      rw [ha2_eq, hb2_eq]
      exact thm_10_9_one_one u_a2 u_b2
    have ha_ndvd_b : ¬ (a ∣ b) := by
      intro h; rcases hb.eq_one_or_self_of_dvd a h with h1 | h1
      · exact ha.one_lt.ne' h1
      · exact hab h1
    have hnum_b_at_a : ¬ (a ∣ (b' : ℚ).num.natAbs) := by
      simp only [b', Units.val_mk0, Rat.num_natCast, Int.natAbs_natCast]; exact ha_ndvd_b
    have hden_b_at_a : ¬ (a ∣ (b' : ℚ).den) := by
      simp only [b', Units.val_mk0, Rat.den_natCast]
      exact fun h => ha.one_lt.ne' (Nat.eq_one_of_dvd_one h)
    obtain ⟨ub_a, hub_a⟩ := ratToQpUnits_eq_unitZpToQp_of_not_dvd a b' hnum_b_at_a hden_b_at_a
    have hf_pa : f pa = padicUnitLegendre ub_a := by
      simp only [f, pa]
      unfold hilbertAtPrime
      rw [ratToQpUnits_natPrime_eq_qpPrime a, hub_a]
      exact hilbert_p_unit_eq_legendre ha_odd ub_a
    have hb_ndvd_a : ¬ (b ∣ a) := by
      intro h; rcases ha.eq_one_or_self_of_dvd b h with h1 | h1
      · exact hb.one_lt.ne' h1
      · exact hab h1.symm
    have hnum_a_at_b : ¬ (b ∣ (a' : ℚ).num.natAbs) := by
      simp only [a', Units.val_mk0, Rat.num_natCast, Int.natAbs_natCast]; exact hb_ndvd_a
    have hden_a_at_b : ¬ (b ∣ (a' : ℚ).den) := by
      simp only [a', Units.val_mk0, Rat.den_natCast]
      exact fun h => hb.one_lt.ne' (Nat.eq_one_of_dvd_one h)
    obtain ⟨ua_b, hua_b⟩ := ratToQpUnits_eq_unitZpToQp_of_not_dvd b a' hnum_a_at_b hden_a_at_b
    have hf_pb : f pb = padicUnitLegendre ua_b := by
      simp only [f, pb]
      unfold hilbertAtPrime
      rw [hua_b, ratToQpUnits_natPrime_eq_qpPrime b]
      show padicHilbertSymbol b (unitZpToQp ua_b) (qpPrime b) = padicUnitLegendre ua_b
      rw [show padicHilbertSymbol b (unitZpToQp ua_b) (qpPrime b) =
        padicHilbertSymbol b (qpPrime b) (unitZpToQp ua_b) from by
        unfold padicHilbertSymbol; exact hilbertSymbol.symm _ _]
      exact hilbert_p_unit_eq_legendre hb_odd ua_b
    rw [hinfty, hf_two, hf_pa, hf_pb]
    simp only [one_mul]
    exact hilbert_qr_cancellation ha hb ha_odd hb_odd hab u_a2 u_b2 hu_a2 hu_b2 ub_a hub_a ua_b hua_b

/--
[hilbert_product_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean)
-/
@[path]
lemma hilbert_product_formula
  {a b : ℚˣ} :
-- imply
  globalHilbertProduct a b = 1 := by
-- proof
  exact hilbert_product_formula_bilinearity_reduction a b
    hilbert_product_neg_one_neg_one
    (fun q hq => hilbert_product_neg_one_prime q hq)
    (fun q hq => hilbert_product_prime_self q hq)
    (fun q hq hq_odd => hilbert_product_two_odd_prime q hq hq_odd)
    (fun a b ha hb ha_odd hb_odd hab => hilbert_product_distinct_odd_primes a b ha hb ha_odd hb_odd hab)


-- created on 2026-10-23
