import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[eval_zero_eq_one_of_isCoprime_X](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/OddPerfectPolynomial.lean)
-/
@[path]
private lemma eval_zero_eq_one_of_isCoprime_X
  (p : Polynomial (ZMod 2))
  (h : IsCoprime p Polynomial.X) :
  p.eval 0 = 1 := by
  have hmap := h.map (Polynomial.evalRingHom (0 : ZMod 2))
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_X] at hmap
  have hu : IsUnit (p.eval 0) := isCoprime_zero_right.mp hmap
  have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  obtain h0 | h1 := h2 (p.eval 0)
  · exfalso
    rw [h0] at hu
    exact not_isUnit_zero hu
  · exact h1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[odd_perfect_polynomial_is_square](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/OddPerfectPolynomial.lean)
-/
@[path]
lemma odd_perfect_polynomial_is_square
  {A : Polynomial (ZMod 2)}
-- given
  (hodd : IsCoprime A Polynomial.X ∧ IsCoprime A (Polynomial.X + 1))
  (hperfect : (finsum fun d : {d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A} => (d : Polynomial (ZMod 2))) = A) :
-- imply
  IsSquare A := by
-- proof
  obtain ⟨hoddX, -⟩ := hodd
  have hAeval : A.eval 0 = 1 := eval_zero_eq_one_of_isCoprime_X A hoddX
  have hA0 : A ≠ 0 := by
    rintro rfl
    simp at hAeval
  have hAmonic : A.Monic := by
    have hlc : A.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hA0
    have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    obtain h | h := h2 A.leadingCoeff
    · exact absurd h hlc
    · exact h
  haveI : Fintype { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A } :=
    Polynomial.fintypeSubtypeMonicDvd A hA0
  rw [finsum_eq_sum_of_fintype] at hperfect
  have hterm : ∀ d : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A }, d.val.eval 0 = 1 :=
    fun d => eval_zero_eq_one_of_isCoprime_X d.val
      (hoddX.of_isCoprime_of_dvd_left d.2.2)
  have hsum0 : (∑ _x : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A }, (1 : ZMod 2)) = 1 := by
    have hcongr := congrArg ⇑(Polynomial.evalRingHom (0 : ZMod 2)) hperfect
    rw [map_sum] at hcongr
    simp only [Polynomial.coe_evalRingHom] at hcongr
    rw [hAeval] at hcongr
    simpa only [hterm] using hcongr
  have hφmonic : ∀ d : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A }, (A / d.val).Monic := by
    intro d
    have hd0 : d.val ≠ 0 := d.2.1.ne_zero
    have hmul : d.val * (A / d.val) = A := EuclideanDomain.mul_div_cancel' hd0 d.2.2
    have hAm : (d.val * (A / d.val)).Monic := by
      rwa [hmul]
    exact d.2.1.of_mul_monic_left hAm
  have hφdvd : ∀ d : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A }, (A / d.val) ∣ A := by
    intro d
    have hd0 : d.val ≠ 0 := d.2.1.ne_zero
    have hmul : d.val * (A / d.val) = A := EuclideanDomain.mul_div_cancel' hd0 d.2.2
    have heq : A = A / d.val * d.val := hmul.symm.trans (mul_comm d.val (A / d.val))
    exact ⟨d.val, heq⟩
  have hdivinv : ∀ d : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A },
    A / (A / d.val) = d.val := by
    intro d
    have hd0 : d.val ≠ 0 := d.2.1.ne_zero
    have he0 : A / d.val ≠ 0 := (hφmonic d).ne_zero
    rw [EuclideanDomain.div_eq_iff_eq_mul_of_dvd _ _ _ he0 (hφdvd d)]
    have hmul : d.val * (A / d.val) = A := EuclideanDomain.mul_div_cancel' hd0 d.2.2
    exact hmul.symm.trans (mul_comm d.val (A / d.val))
  have hex : ∃ d : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A }, A / d.val = d.val := by
    by_contra hcon
    have hcon' : ∀ d : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A }, A / d.val ≠ d.val :=
      fun d h => hcon ⟨d, h⟩
    have hzero : (∑ _x : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A }, (1 : ZMod 2)) = 0 := by
      refine Finset.sum_involution
        (fun (a : { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A }) (_ : a ∈ Finset.univ) =>
          (⟨A / a.val, hφmonic a, hφdvd a⟩ :
            { d : Polynomial (ZMod 2) // d.Monic ∧ d ∣ A })) ?_ ?_ ?_ ?_
      · intro a ha
        show (1 : ZMod 2) + 1 = 0
        decide
      · intro a ha _ hcontra
        have hcontra' : A / a.val = a.val := congrArg Subtype.val hcontra
        exact hcon' a hcontra'
      · intro a ha
        exact Finset.mem_univ _
      · intro a ha
        have hsub : A / (A / a.val) = a.val := hdivinv a
        apply Subtype.ext
        exact hsub
    rw [hsum0] at hzero
    exact one_ne_zero hzero
  obtain ⟨d, hd⟩ := hex
  have hd0 : d.val ≠ 0 := d.2.1.ne_zero
  have hdsq : A = d.val * d.val := by
    rwa [EuclideanDomain.div_eq_iff_eq_mul_of_dvd _ _ _ hd0 d.2.2] at hd
  exact isSquare_iff_exists_mul_self A |>.mpr ⟨d.val, hdsq⟩

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
