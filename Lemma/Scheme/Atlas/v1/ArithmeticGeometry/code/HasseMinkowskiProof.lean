import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.HasseMinkowskiProof.Part3
open hilbertSymbol
open scoped Classical
open HilbertSymbol
open Matrix


/--
[rat_isSolvable_implies_padic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma rat_isSolvable_implies_padic
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {b c : ℚˣ}
-- given
  (h : HilbertSymbol.IsSolvable ℚ b c) :
-- imply
  HilbertSymbol.IsSolvable ℚ_[p] (ratToQpUnits p b) (ratToQpUnits p c) := by
-- proof
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨(x : ℚ_[p]), (y : ℚ_[p]), ?_⟩
  have hb_val : (ratToQpUnits p b : ℚ_[p]) = ((b : ℚ) : ℚ_[p]) := ratToQpUnits_val p b
  have hc_val : (ratToQpUnits p c : ℚ_[p]) = ((c : ℚ) : ℚ_[p]) := ratToQpUnits_val p c
  rw [hb_val, hc_val]
  exact_mod_cast hxy

/--
[rat_hilbert_one_implies_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma rat_hilbert_one_implies_local
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {b c : ℚˣ}
-- given
  (h : hilbertSymbol ℚ b c = 1) :
-- imply
  hilbertAtPrime p b c = 1 := by
-- proof
  rw [hilbertSymbol.eq_one_iff] at h
  simp only [hilbertAtPrime, padicHilbertSymbol, hilbertSymbol.eq_one_iff]
  exact rat_isSolvable_implies_padic p b c h
namespace hilbertSymbol
variable {F : Type*} [Field F]

namespace hilbertSymbol

/--
[self_neg_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma self_neg_self
  [Field F]
  [NeZero (2 : F)]
  {x : Fˣ} :
-- imply
  hilbertSymbol F x (-x) = 1 := by
-- proof
  rw [eq_one_iff]
  refine ⟨((x : F)⁻¹ + 1) / 2, ((x : F)⁻¹ - 1) / 2, ?_⟩
  have hx : (x : F) ≠ 0 := x.ne_zero
  simp only [Units.val_neg]
  field_simp
  ring

end hilbertSymbol

namespace hilbertSymbol

/--
[IsSolvable_sq_mul_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma IsSolvable_sq_mul_left
  [Field F]
  {a b c : Fˣ} :
-- imply
  HilbertSymbol.IsSolvable F (a * c * c) b ↔ HilbertSymbol.IsSolvable F a b := by
-- proof
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨(c : F) * x, y, by
      simp only [Units.val_mul] at h ⊢
      have : ↑a * (↑c * x) ^ 2 = ↑a * ↑c * ↑c * x ^ 2 := by ring
      rw [this]; exact h⟩
  · rintro ⟨x, y, h⟩
    refine ⟨(↑c)⁻¹ * x, y, ?_⟩
    simp only [Units.val_mul] at h ⊢
    have hc : (c : F) ≠ 0 := c.ne_zero
    have key : ↑a * ↑c * ↑c * ((↑c : F)⁻¹ * x) ^ 2 = ↑a * x ^ 2 := by field_simp
    rw [key]; exact h

end hilbertSymbol

namespace hilbertSymbol

/--
[IsSolvable_sq_mul_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma IsSolvable_sq_mul_right
  [Field F]
  {a b c : Fˣ} :
-- imply
  HilbertSymbol.IsSolvable F a (b * c * c) ↔ HilbertSymbol.IsSolvable F a b := by
-- proof
  have comm : ∀ u v : Fˣ, HilbertSymbol.IsSolvable F u v ↔ HilbertSymbol.IsSolvable F v u := by
    intro u v
    constructor
    · rintro ⟨x, y, h⟩; exact ⟨y, x, by rw [add_comm]; exact h⟩
    · rintro ⟨x, y, h⟩; exact ⟨y, x, by rw [add_comm]; exact h⟩
  rw [comm, IsSolvable_sq_mul_left, comm]

end hilbertSymbol

namespace hilbertSymbol

/--
[sq_mul_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma sq_mul_left
  [Field F]
  {a c b : Fˣ} :
-- imply
  hilbertSymbol F (a * c * c) b = hilbertSymbol F a b := by
-- proof
  unfold hilbertSymbol
  simp only [IsSolvable_sq_mul_left]

end hilbertSymbol

namespace hilbertSymbol

/--
[sq_mul_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma sq_mul_right
  [Field F]
  {a b c : Fˣ} :
-- imply
  hilbertSymbol F a (b * c * c) = hilbertSymbol F a b := by
-- proof
  unfold hilbertSymbol
  simp only [IsSolvable_sq_mul_right]

end hilbertSymbol

namespace hilbertSymbol

/--
[div_div_eq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma div_div_eq_mul
  [Field F]
  [HilbertBilinearField F]
  {a b t : Fˣ} :
-- imply
  hilbertSymbol F (a * t⁻¹) (b * t⁻¹) = hilbertSymbol F a b * hilbertSymbol F t (-(a * b)) := by
-- proof
  have sq_inv : hilbertSymbol F (a * t⁻¹) (b * t⁻¹) = hilbertSymbol F (a * t) (b * t) := by
    have h1 : a * t = a * t⁻¹ * t * t := by group
    have h2 : b * t = b * t⁻¹ * t * t := by group
    rw [h1, h2, sq_mul_left, sq_mul_right]
  rw [sq_inv, mul_left, mul_right a b t, mul_right t b t, symm a t]
  have rearr : hilbertSymbol F a b * hilbertSymbol F t a *
    (hilbertSymbol F t b * hilbertSymbol F t t) =
    hilbertSymbol F a b * (hilbertSymbol F t a * hilbertSymbol F t b *
    hilbertSymbol F t t) := by ring
  rw [rearr, ← mul_right t a b, ← mul_right t (a * b) t]
  congr 1
  have absorb : hilbertSymbol F t (a * b * t) = hilbertSymbol F t (a * b * t * (-t)) := by
    have h1 := mul_right t (a * b * t) (-t)
    rw [h1, self_neg_self, mul_one]
  have unit_eq : a * b * t * (-t) = -(a * b) * t * t := by
    ext; simp only [Units.val_mul, Units.val_neg]; ring
  rw [absorb, unit_eq, sq_mul_right]

end hilbertSymbol

namespace hilbertSymbol

/--
[prod_pm_one_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma prod_pm_one_eq_one_iff
  [Field F]
  {x y : ℤ}
-- given
  (hx : x = 1 ∨ x = -1)
  (hy : y = 1 ∨ y = -1) :
-- imply
  x * y = 1 ↔ x = y := by
-- proof
  obtain rfl | rfl <;> rcases hy with rfl | rfl <;> simp := hx

end hilbertSymbol

/--
[binary_form_represents_iff_hilbert](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma binary_form_represents_iff_hilbert
  [Field F]
  [HilbertBilinearField F]
  {a b t : Fˣ} :
-- imply
  BinaryForm.Represents F a b (t : F) ↔ hilbertSymbol F a b = hilbertSymbol F t (-(a * b)) := by
-- proof
  have represents_iff_solvable :
    BinaryForm.Represents F a b (t : F) ↔
    HilbertSymbol.IsSolvable F (a * t⁻¹) (b * t⁻¹) := by
    constructor
    · rintro ⟨x, y, h⟩
      refine ⟨x, y, ?_⟩
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      have ht : (t : F) ≠ 0 := t.ne_zero
      field_simp
      exact h
    · rintro ⟨x, y, h⟩
      refine ⟨x, y, ?_⟩
      simp only [Units.val_mul, Units.val_inv_eq_inv_val] at h
      have ht : (t : F) ≠ 0 := t.ne_zero
      field_simp at h
      exact h
  have solvable_iff_one :
    HilbertSymbol.IsSolvable F (a * t⁻¹) (b * t⁻¹) ↔
    hilbertSymbol F (a * t⁻¹) (b * t⁻¹) = 1 :=
    (hilbertSymbol.eq_one_iff).symm
  rwa [represents_iff_solvable, solvable_iff_one, hilbertSymbol.div_div_eq_mul]
    (hilbertSymbol.eq_one_or_neg_one a b)
    (hilbertSymbol.eq_one_or_neg_one t (-(a * b)))
section Corollary114
variable {F : Type*} [Field F] [HilbertBilinearField F]

/--
[BinaryForm.Represents.ternary_represents_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma BinaryForm.Represents.ternary_represents_zero
  [Field F]
  [HilbertBilinearField F]
  {a b c : Fˣ}
-- given
  (h : BinaryForm.Represents F a b ((-c : Fˣ) : F)) :
-- imply
  TernaryForm.RepresentsZero F a b c := by
-- proof
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨x, y, 1, Or.inr (Or.inr one_ne_zero), ?_⟩
  simp only [Units.val_neg, one_pow, mul_one] at hxy ⊢
  linear_combination hxy

/--
[TernaryForm.RepresentsZero.binary_represents_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma TernaryForm.RepresentsZero.binary_represents_neg
  [Field F]
  [HilbertBilinearField F]
  {a b c : Fˣ}
-- given
  (h : TernaryForm.RepresentsZero F a b c) :
-- imply
  BinaryForm.Represents F a b ((-c : Fˣ) : F) := by
-- proof
  obtain ⟨x, y, z, hne, heq⟩ := h
  by_cases hz : z ≠ 0
  ·
    refine ⟨x / z, y / z, ?_⟩
    simp only [Units.val_neg]
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
    field_simp
    linear_combination heq
  ·
    push Not at hz
    subst hz
    simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] at heq
    have hne' : x ≠ 0 ∨ y ≠ 0 := by
      obtain hx | hy | hz' := hne
      · exact Or.inl hx
      · exact Or.inr hy
      · exact absurd rfl hz'
    obtain hx | hy := hne'
    · exact HilbertSymbol.binary_form_represents_all hx heq ((-c : Fˣ) : F)
    ·
      by_cases hx : x ≠ 0
      · exact HilbertSymbol.binary_form_represents_all hx heq ((-c : Fˣ) : F)
      · push Not at hx
        subst hx
        simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add] at heq
        exfalso
        have : (b : F) * y ^ 2 ≠ 0 :=
          mul_ne_zero b.ne_zero (pow_ne_zero 2 hy)
        exact this heq

/--
[ternary_represents_zero_iff_binary_represents_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma ternary_represents_zero_iff_binary_represents_neg
  [Field F]
  [HilbertBilinearField F]
  {a b c : Fˣ} :
-- imply
  TernaryForm.RepresentsZero F a b c ↔ BinaryForm.Represents F a b ((-c : Fˣ) : F) :=
-- proof
  ⟨TernaryForm.RepresentsZero.binary_represents_neg,
    BinaryForm.Represents.ternary_represents_zero⟩

/--
[ternary_form_represents_zero_iff_hilbert](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma ternary_form_represents_zero_iff_hilbert
  [Field F]
  [HilbertBilinearField F]
  {a b c : Fˣ} :
-- imply
  TernaryForm.RepresentsZero F a b c ↔ hilbertSymbol F a b = hilbertSymbol F (-c) (-(a * b)) := by
-- proof
  rw [ternary_represents_zero_iff_binary_represents_neg,
    binary_form_represents_iff_hilbert a b (-c)]
end Corollary114
section Corollary112

/--
[int_padicNorm_eq_one_cofinitely](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma int_padicNorm_eq_one_cofinitely
  {a : ℤ}
-- given
  (ha : a ≠ 0) :
-- imply
  Set.Finite {p : ℕ | p.Prime ∧ padicNorm p (a : ℚ) ≠ 1} := by
-- proof
  apply Set.Finite.subset (Set.finite_Icc 0 a.natAbs)
  intro p ⟨hp, hne⟩
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : (p : ℤ) ∣ a := by
    by_contra hndvd; exact hne ((padicNorm.int_eq_one_iff a).mpr hndvd)
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr ha)
    (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdvd))

/--
[nat_padicNorm_eq_one_cofinitely](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma nat_padicNorm_eq_one_cofinitely
  {d : ℕ}
-- given
  (hd : d ≠ 0) :
-- imply
  Set.Finite {p : ℕ | p.Prime ∧ padicNorm p (d : ℚ) ≠ 1} := by
-- proof
  apply Set.Finite.subset (Set.finite_Icc 0 d)
  intro p ⟨hp, hne⟩
  simp only [Set.mem_Icc]
  refine ⟨Nat.zero_le _, ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ d := by
    by_contra hndvd; exact hne ((padicNorm.nat_eq_one_iff d).mpr hndvd)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hdvd

/--
[rat_padicNorm_eq_one_cofinitely](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma rat_padicNorm_eq_one_cofinitely
  {q : ℚ}
-- given
  (hq : q ≠ 0) :
-- imply
  Set.Finite {p : ℕ | p.Prime ∧ padicNorm p q ≠ 1} := by
-- proof
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hden : q.den ≠ 0 := Nat.pos_iff_ne_zero.mp q.pos
  apply Set.Finite.subset (Set.Finite.union
    (int_padicNorm_eq_one_cofinitely q.num hnum)
    (nat_padicNorm_eq_one_cofinitely q.den hden))
  intro p ⟨hp, hne⟩
  haveI : Fact p.Prime := ⟨hp⟩
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_contra hall
  simp only [not_or, not_and] at hall
  have hnum_ok : padicNorm p (q.num : ℚ) = 1 := not_not.mp (hall.1 hp)
  have hden_ok : padicNorm p (q.den : ℚ) = 1 := not_not.mp (hall.2 hp)
  apply hne
  conv_lhs => rw [show q = (q.num : ℚ) / q.den from by rw [Rat.num_div_den]]
  rw [padicNorm.div, hnum_ok, hden_ok, div_one]

/--
[finitely_many_bad_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma finitely_many_bad_primes
  {n : ℕ}
  {w : Fin n → ℚ}
-- given
  (hw : ∀ i, w i ≠ 0) :
-- imply
  Set.Finite {p : ℕ | p.Prime ∧ ∃ i, padicNorm p (w i) ≠ 1} := by
-- proof
  apply Set.Finite.subset (Set.finite_iUnion
    (fun i => rat_padicNorm_eq_one_cofinitely (w i) (hw i)))
  intro p ⟨hp, i, hne⟩
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨i, hp, hne⟩

/--
[padicNorm_eq_one_to_padic_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma padicNorm_eq_one_to_padic_norm
  {p : ℕ}
  [Fact p.Prime]
  {q : ℚ}
-- given
  (h : padicNorm p q = 1) :
-- imply
  ‖(q : ℚ_[p])‖ = 1 := by
-- proof
  rw [Padic.eq_padicNorm]
  simp [h]

/--
[diagonal_form_represents_zero_locally_cofinitely](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma diagonal_form_represents_zero_locally_cofinitely
  {n : ℕ}
  {w : Fin n → ℚ}
-- given
  (hn : 2 < n)
  (hw : ∀ i, w i ≠ 0) :
-- imply
  ∃ S : Finset ℕ, ∀ (p : ℕ) (_ : p.Prime) (_ : p ∉ S), haveI : Fact p.Prime :=
-- proof
  ⟨‹Nat.Prime p›⟩
    ∃ x : Fin n → ℚ_[p], (∃ i, x i ≠ 0) ∧
      ∑ i, (w i : ℚ_[p]) * x i ^ 2 = 0 := by
    have hfin : Set.Finite ({2} ∪ {p : ℕ | p.Prime ∧ ∃ i, padicNorm p (w i) ≠ 1}) :=
      Set.Finite.union (Set.finite_singleton 2) (finitely_many_bad_primes w hw)
    refine ⟨hfin.toFinset, fun p hp hpS => ?_⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have hp_ne_2 : p ≠ 2 := by
      intro h; subst h
      apply hpS; rw [Set.Finite.mem_toFinset]; exact Set.mem_union_left _ rfl
    have hw_norm : ∀ i, padicNorm p (w i) = 1 := by
      intro i
      by_contra hi
      apply hpS; rw [Set.Finite.mem_toFinset]
      exact Set.mem_union_right _ ⟨hp, i, hi⟩
    have hw_pnorm : ∀ i, ‖(w i : ℚ_[p])‖ = 1 :=
      fun i => padicNorm_eq_one_to_padic_norm (w i) (hw_norm i)
    set a : Fin n → ℤ_[p]ˣ := fun i => PadicInt.mkUnits (hw_pnorm i) with ha_def
    obtain ⟨x, hne, hsum⟩ := diagonal_unit_form_represents_zero hp_ne_2 hn a
    refine ⟨x, hne, ?_⟩
    convert hsum using 1
end Corollary112
section Corollary115
open HilbertSymbol
noncomputable section

/--
[Corollary115.hilbert_product_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma Corollary115.hilbert_product_formula
  {a b : ℚˣ} :
-- imply
  Corollary115.globalHilbertProduct a b = 1 := by
-- proof
  show globalHilbertProduct a b = 1
  exact _root_.hilbert_product_formula a b

/--
[Corollary115.hilbert_product_formula_finite_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma Corollary115.hilbert_product_formula_finite_support
  {a b : ℚˣ} :
-- imply
  (Function.mulSupport (fun p : Nat.Primes => haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩ Corollary115.hilbertAtPrime p.val a b)).Finite := by
-- proof
  have h := _root_.hilbert_product_formula_finite_support a b
  rwa [Set.Finite] at h

/--
[hilbertAt_eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma hilbertAt_eq_one_or_neg_one
  {v : Place}
  {a b : ℚˣ} :
-- imply
  hilbertAt v a b = 1 ∨ hilbertAt v a b = -1 := by
-- proof
  cases v with
  | infty =>
    simp only [hilbertAt, Corollary115.hilbertAtInfty, realHilbertSymbol]
    exact hilbertSymbol.eq_one_or_neg_one _ _
  | finite p =>
    simp only [hilbertAt, Corollary115.hilbertAtPrime, padicHilbertSymbol]
    exact hilbertSymbol.eq_one_or_neg_one _ _

/--
[globalHilbertProduct_eq_hilbertAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma globalHilbertProduct_eq_hilbertAt
  {a b : ℚˣ} :
-- imply
  Corollary115.globalHilbertProduct a b = hilbertAt Place.infty a b * ∏ᶠ (p : Nat.Primes), hilbertAt (Place.finite p) a b := by
-- proof
  unfold Corollary115.globalHilbertProduct hilbertAt
  rfl

/--
[hilbert_symbol_determined_by_all_but_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma hilbert_symbol_determined_by_all_but_one
  {a b c d : ℚˣ}
  {v₀ : Place}
-- given
  (hprod1 : Corollary115.globalHilbertProduct a b = 1)
  (hprod2 : Corollary115.globalHilbertProduct c d = 1)
  (h_agree : ∀ v : Place, v ≠ v₀ → hilbertAt v a b = hilbertAt v c d) :
-- imply
  hilbertAt v₀ a b = hilbertAt v₀ c d := by
-- proof
  rw [globalHilbertProduct_eq_hilbertAt] at hprod1 hprod2
  cases v₀ with
  | infty =>
    have hfin : ∀ p : Nat.Primes, hilbertAt (Place.finite p) a b =
      hilbertAt (Place.finite p) c d :=
      fun p => h_agree (Place.finite p) (by simp)
    have hprod_eq : ∏ᶠ (p : Nat.Primes), hilbertAt (Place.finite p) a b =
      ∏ᶠ (p : Nat.Primes), hilbertAt (Place.finite p) c d :=
      finprod_congr hfin
    have h1 := hprod1
    have h2 := hprod2
    rw [hprod_eq] at h1
    have hne : ∏ᶠ (p : Nat.Primes), hilbertAt (Place.finite p) c d ≠ 0 := by
      intro heq; rw [heq, mul_zero] at h2; exact one_ne_zero h2.symm
    exact mul_right_cancel₀ hne (by rw [h1, h2])
  | finite p₀ =>
    have hinfty : hilbertAt Place.infty a b = hilbertAt Place.infty c d :=
      h_agree Place.infty (by simp)
    have hfin : ∀ p : Nat.Primes, p ≠ p₀ →
      hilbertAt (Place.finite p) a b = hilbertAt (Place.finite p) c d :=
      fun p hp => h_agree (Place.finite p) (by simp [hp])
    rw [hinfty] at hprod1
    have hne_infty : hilbertAt Place.infty c d ≠ 0 := by
      intro heq; rw [heq, zero_mul] at hprod2; exact one_ne_zero hprod2.symm
    have hprod_fin_eq : ∏ᶠ (p : Nat.Primes), hilbertAt (Place.finite p) a b =
      ∏ᶠ (p : Nat.Primes), hilbertAt (Place.finite p) c d :=
      mul_left_cancel₀ hne_infty (by rw [hprod1, hprod2])
    have hsupp1 : (Function.mulSupport
      (fun p => hilbertAt (Place.finite p) a b)).Finite :=
      Corollary115.hilbert_product_formula_finite_support a b
    have hsupp2 : (Function.mulSupport
      (fun p => hilbertAt (Place.finite p) c d)).Finite :=
      Corollary115.hilbert_product_formula_finite_support c d
    set S := hsupp1.toFinset ∪ hsupp2.toFinset ∪ {p₀} with hS_def
    have hfS : Function.mulSupport (fun p => hilbertAt (Place.finite p) a b) ⊆ ↑S := by
      intro x hx
      simp only [hS_def, Finset.coe_union, Finset.coe_singleton,
        Set.mem_union, Set.mem_singleton_iff]
      left; left; exact (Set.Finite.mem_toFinset hsupp1).mpr hx
    have hgS : Function.mulSupport (fun p => hilbertAt (Place.finite p) c d) ⊆ ↑S := by
      intro x hx
      simp only [hS_def, Finset.coe_union, Finset.coe_singleton,
        Set.mem_union, Set.mem_singleton_iff]
      left; right; exact (Set.Finite.mem_toFinset hsupp2).mpr hx
    rw [finprod_eq_prod_of_mulSupport_subset _ hfS,
      finprod_eq_prod_of_mulSupport_subset _ hgS] at hprod_fin_eq
    have hp₀S : p₀ ∈ S := by simp [hS_def]
    rw [← Finset.mul_prod_erase S _ hp₀S,
      ← Finset.mul_prod_erase S _ hp₀S] at hprod_fin_eq
    have hrest : ∏ i ∈ S.erase p₀, (fun p => hilbertAt (Place.finite p) a b) i =
      ∏ i ∈ S.erase p₀, (fun p => hilbertAt (Place.finite p) c d) i :=
      Finset.prod_congr rfl (fun x hx => hfin x (Finset.ne_of_mem_erase hx))
    rw [hrest] at hprod_fin_eq
    have hP_ne : ∏ i ∈ S.erase p₀,
      (fun p => hilbertAt (Place.finite p) c d) i ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro x _
      obtain h | h <;> simp [h] := hilbertAt_eq_one_or_neg_one (Place.finite x) c d
    exact mul_right_cancel₀ hP_ne hprod_fin_eq

/--
[corollary_11_5](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean)
-/
@[path]
lemma corollary_11_5
  {a b c : ℚˣ}
  {v₀ : Place}
-- given
  (h : ∀ v : Place, v ≠ v₀ → hilbertAt v a b = hilbertAt v (-c) (-(a * b))) :
-- imply
  hilbertAt v₀ a b = hilbertAt v₀ (-c) (-(a * b)) :=
-- proof
  hilbert_symbol_determined_by_all_but_one a b (-c) (-(a * b))
    (Corollary115.hilbert_product_formula a b)
    (Corollary115.hilbert_product_formula (-c) (-(a * b)))
    v₀ h
end
end Corollary115
section Corollary112General
open Matrix


-- created on 2026-10-23
