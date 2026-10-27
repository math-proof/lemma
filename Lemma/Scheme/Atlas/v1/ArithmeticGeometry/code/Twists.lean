import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.ArithmeticGeometry.code.Twists.Part2
open AlgebraicGeometry CategoryTheory Limits ArithmeticGeometry


namespace ArithmeticGeometry

/--
[AreTwists.refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Twists.lean)
-/
@[path]
lemma AreTwists.refl
  {k : Type u}
  [Field k]
  {k}
  {X : Scheme.{u}}
  [X.Over (specOf k)] :
-- imply
  AreTwists k X X :=
-- proof
  ⟨Iso.refl _⟩

end ArithmeticGeometry

namespace ArithmeticGeometry

/--
[AreTwists.symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Twists.lean)
-/
@[path]
lemma AreTwists.symm
  {k : Type u}
  [Field k]
  {k}
  {X Y : Scheme.{u}}
  [X.Over (specOf k)]
  [Y.Over (specOf k)]
-- given
  (h : AreTwists k X Y) :
-- imply
  AreTwists k Y X :=
-- proof
  h.map Iso.symm

end ArithmeticGeometry

namespace ArithmeticGeometry

/--
[AreTwists.trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Twists.lean)
-/
@[path]
lemma AreTwists.trans
  {k : Type u}
  [Field k]
  {k}
  {X Y Z : Scheme.{u}}
  [X.Over (specOf k)]
  [Y.Over (specOf k)]
  [Z.Over (specOf k)]
-- given
  (hXY : AreTwists k X Y)
  (hYZ : AreTwists k Y Z) :
-- imply
  AreTwists k X Z := by
-- proof
  obtain ⟨f⟩ := hXY
  obtain ⟨g⟩ := hYZ
  exact ⟨f ≪≫ g⟩
end ArithmeticGeometry
section GenusOneTwist
universe v


/--
[GenusOneCurve.exists_ellipticCurve_twist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Twists.lean)
-/
@[path]
lemma GenusOneCurve.exists_ellipticCurve_twist
  {k : Type v}
  [Field k]
  {k : Type v}
  [Field k]
  {C : GenusOneCurve k} :
-- imply
  ∃ E : EllipticCurveOver k, C.IsTwistOfEllipticCurve E := by
-- proof
  obtain ⟨E, hE⟩ := j_invariant_surjective C.jInvariant
  refine ⟨E, ?_⟩
  rw [IsTwistOfEllipticCurve]
  haveI := C.Jacobian.isElliptic
  haveI := E.isElliptic
  exact isomorphic_over_closure_of_j_eq C.Jacobian.curve E.curve hE.symm

/--
[Rat.no_fourth_root_of_four](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Twists.lean)
-/
@[path]
lemma Rat.no_fourth_root_of_four
  {k : Type v}
  [Field k] :
-- imply
  ∀ q : ℚ, q ^ 4 ≠ 4 := by
-- proof
  intro q hq
  have hcop : Int.gcd q.num q.den = 1 := q.reduced
  have h1 : (q.num : ℚ) ^ 4 = 4 * (q.den : ℚ) ^ 4 := by
    have : q = q.num / q.den := (Rat.num_div_den q).symm
    rw [this] at hq; field_simp at hq; linarith
  have h2 : q.num ^ 4 = 4 * (q.den : ℤ) ^ 4 := by exact_mod_cast h1
  have h_2_num : (2 : ℤ) ∣ q.num := by
    have hdvd : (2 : ℤ) ∣ q.num ^ (4 : ℕ) := ⟨2 * (q.den : ℤ) ^ 4, by linarith⟩
    exact Prime.dvd_of_dvd_pow Int.prime_two hdvd
  have h_2_den : (2 : ℤ) ∣ (q.den : ℤ) := by
    obtain ⟨m, hm⟩ := h_2_num
    have hd4 : (q.den : ℤ) ^ (4 : ℕ) = 4 * m ^ (4 : ℕ) := by have := hm ▸ h2; nlinarith
    have hdvd : (2 : ℤ) ∣ (q.den : ℤ) ^ (4 : ℕ) := ⟨2 * m ^ (4 : ℕ), by linarith [hd4]⟩
    exact Prime.dvd_of_dvd_pow Int.prime_two hdvd
  have : (2 : ℕ) ∣ Int.gcd q.num q.den := by exact_mod_cast Int.dvd_gcd h_2_num h_2_den
  rw [hcop] at this; omega

/--
[not_iso_y2x3mx_y2x3m4x](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Twists.lean)
-/
@[path]
lemma not_iso_y2x3mx_y2x3m4x
  {k : Type v}
  [Field k] :
-- imply
  ¬∃ σ : WeierstrassCurve.VariableChange ℚ, (WeierstrassCurve.mk 0 0 0 (-1) 0 : WeierstrassCurve ℚ) = σ • (WeierstrassCurve.mk 0 0 0 (-4) 0 : WeierstrassCurve ℚ) := by
-- proof
  rintro ⟨σ, h⟩
  have ha₁ := congr_arg WeierstrassCurve.a₁ h
  have ha₂ := congr_arg WeierstrassCurve.a₂ h
  have ha₃ := congr_arg WeierstrassCurve.a₃ h
  have ha₄ := congr_arg WeierstrassCurve.a₄ h
  simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄] at ha₁ ha₂ ha₃ ha₄
  have hu_inv_ne : (σ.u⁻¹ : ℚˣ).val ≠ 0 := σ.u⁻¹.ne_zero
  have hs : σ.s = 0 := by
    have : (↑σ.u⁻¹ : ℚ) * (0 + 2 * σ.s) = 0 := by linarith
    cases mul_eq_zero.mp this with
    | inl h => exact absurd h hu_inv_ne
    | inr h => linarith
  have ht : σ.t = 0 := by
    have : (↑σ.u⁻¹ : ℚ) ^ 3 * (2 * σ.t) = 0 := by ring_nf; ring_nf at ha₃; linarith
    cases mul_eq_zero.mp this with
    | inl h => exact absurd (pow_eq_zero_iff (n := 3) (by omega) |>.mp h) hu_inv_ne
    | inr h => linarith
  have hr : σ.r = 0 := by
    have : (↑σ.u⁻¹ : ℚ) ^ 2 * (3 * σ.r - σ.s ^ 2) = 0 := by
      ring_nf; ring_nf at ha₂; linarith
    cases mul_eq_zero.mp this with
    | inl h => exact absurd (pow_eq_zero_iff (n := 2) (by omega) |>.mp h) hu_inv_ne
    | inr h => nlinarith [hs]
  exact Rat.no_fourth_root_of_four (↑σ.u) (by
    simp only [hs, ht, hr] at ha₄
    have : (↑σ.u⁻¹ : ℚ) ^ 4 * 4 = 1 := by nlinarith
    rw [Units.val_inv_eq_inv_val, inv_pow] at this
    field_simp at this; linarith)


-- created on 2026-10-23
