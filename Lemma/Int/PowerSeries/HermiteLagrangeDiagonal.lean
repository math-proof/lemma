import Mathlib
import Initialize.Tactic.Attr.Basic
open PowerSeries


namespace MetaMathlibExt.LagrangeInversionAux

/--
[map_derivative](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/HermiteLagrangeDiagonal.lean)
-/
@[path]
private lemma map_derivative {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (g : R⟦X⟧) :
  map f (derivative g) = derivative (map f g) := by
  ext n
  simp only [coeff_map, coeff_derivative, map_mul, map_add, map_natCast, map_one]

end MetaMathlibExt.LagrangeInversionAux

namespace MetaMathlibExt.LagrangeInversionAux

/--
[base_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/HermiteLagrangeDiagonal.lean)
-/
@[path]
commutative ring since it only uses `derivative_pow` and the coefficient formulas. -/
private lemma base_mul (R : Type*) [CommRing R] (φ : PowerSeries R) (M : ℕ) :
  ((M + 1 : ℕ) : R) * coeff (M + 1) (φ ^ M * (φ - X * derivative φ)) = 0 := by
  have key : ((M + 1 : ℕ) : PowerSeries R) * (φ ^ M * (φ - X * derivative φ))
    = ((M + 1 : ℕ) : PowerSeries R) * φ ^ (M + 1) - X * derivative (φ ^ (M + 1)) := by
    rw [derivative_pow, Nat.add_sub_cancel]
    ring
  have hc : ((M + 1 : ℕ) : R) * coeff (M + 1) (φ ^ M * (φ - X * derivative φ))
    = coeff (M + 1) (((M + 1 : ℕ) : PowerSeries R) * (φ ^ M * (φ - X * derivative φ))) := by
    rw [show ((M + 1 : ℕ) : PowerSeries R) = C ((M + 1 : ℕ) : R) from
      (map_natCast (C : R →+* PowerSeries R) (M + 1)).symm, coeff_C_mul]
  rw [hc, key, map_sub,
    show ((M + 1 : ℕ) : PowerSeries R) = C ((M + 1 : ℕ) : R) from
      (map_natCast (C : R →+* PowerSeries R) (M + 1)).symm, coeff_C_mul,
    coeff_succ_X_mul, coeff_derivative]
  push_cast
  ring

end MetaMathlibExt.LagrangeInversionAux

namespace MetaMathlibExt.LagrangeInversionAux

/--
[base](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/HermiteLagrangeDiagonal.lean)
-/
@[path]
`base_mul` by transporting the identity through the torsion-free universal ring
`MvPolynomial ℕ ℤ`, where the nonzero factor `N` can be cancelled. -/
private lemma base (R : Type*) [CommRing R] (φ : PowerSeries R) (M : ℕ) :
  coeff (M + 1) (φ ^ M * (φ - X * derivative φ)) = 0 := by
  set 𝕌 := MvPolynomial ℕ ℤ with h𝕌
  set Φ : 𝕌⟦X⟧ := mk fun i => MvPolynomial.X i with hΦdef
  set ev : 𝕌 →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => coeff i φ) with hev
  have hΦ : map ev Φ = φ := by
    ext n
    rw [coeff_map, hΦdef, coeff_mk, hev, MvPolynomial.eval₂Hom_X']
  have hbase𝕌 : coeff (M + 1) (Φ ^ M * (Φ - X * derivative Φ)) = 0 := by
    have h := base_mul 𝕌 Φ M
    have hne : ((M + 1 : ℕ) : 𝕌) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
    exact (mul_eq_zero.mp h).resolve_left hne
  have hexpr : φ ^ M * (φ - X * derivative φ) = map ev (Φ ^ M * (Φ - X * derivative Φ)) := by
    simp only [map_mul, map_pow, map_sub, map_derivative, hΦ, PowerSeries.map_X]
  rw [hexpr, coeff_map, hbase𝕌, map_zero]

end MetaMathlibExt.LagrangeInversionAux

namespace MetaMathlibExt.LagrangeInversionAux

/--
[need0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/HermiteLagrangeDiagonal.lean)
-/
@[path]
term) is the `0`-th coefficient of `F`. -/
private lemma need0 {R : Type*} [CommRing R] (w : PowerSeries R)
  (hw0 : PowerSeries.constantCoeff w = 0) (F : PowerSeries R) :
  coeff 0 (F.subst w) = coeff 0 F := by
  have hs : HasSubst w := HasSubst.of_constantCoeff_zero' hw0
  rw [coeff_subst' hs F 0]
  rw [finsum_eq_single _ 0 (fun d hd => by
    rw [coeff_zero_eq_constantCoeff, map_pow, hw0, zero_pow hd, smul_zero])]
  simp [coeff_zero_eq_constantCoeff]

end MetaMathlibExt.LagrangeInversionAux

namespace MetaMathlibExt.LagrangeInversionAux

/--
[hFsub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/HermiteLagrangeDiagonal.lean)
-/
@[path]
`F(w) = F(0) + X · (φ · F₁)(w)`, where `F₁` is the shift of `F`. -/
private lemma hFsub {R : Type*} [CommRing R] (φ w : PowerSeries R)
  (hw0 : PowerSeries.constantCoeff w = 0) (hw : w = X * φ.subst w) (F : PowerSeries R) :
  F.subst w = C (coeff 0 F) + X * ((φ * (mk fun i => coeff (i + 1) F)).subst w) := by
  have hs : HasSubst w := HasSubst.of_constantCoeff_zero' hw0
  set F₁ : PowerSeries R := mk fun i => coeff (i + 1) F with hF₁
  have hsplit : F = C (coeff 0 F) + X * F₁ := by
    ext n
    cases n with
    | zero => simp [hF₁]
    | succ m => simp [hF₁, coeff_succ_C, coeff_succ_X_mul, coeff_mk]
  have hww : w * (F₁.subst w) = X * ((φ * F₁).subst w) := by
    rw [subst_mul hs, ← mul_assoc, ← hw]
  conv_lhs => rw [hsplit]
  rw [subst_add hs, subst_mul hs, subst_X hs, subst_C, hww, ← C_apply]

end MetaMathlibExt.LagrangeInversionAux

namespace MetaMathlibExt.LagrangeInversionAux

/--
[hrec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/HermiteLagrangeDiagonal.lean)
-/
@[path]
private lemma hrec {R : Type*} [CommRing R] (φ w : PowerSeries R)
  (hw0 : PowerSeries.constantCoeff w = 0) (hw : w = X * φ.subst w) (N : ℕ) (F : PowerSeries R) :
  coeff (N + 1) (F.subst w)
    = coeff N ((φ * (mk fun i => coeff (i + 1) F)).subst w) := by
  rw [hFsub φ w hw0 hw F, map_add, coeff_succ_C, coeff_succ_X_mul, zero_add]

end MetaMathlibExt.LagrangeInversionAux

namespace MetaMathlibExt.LagrangeInversionAux

/--
[needS](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/HermiteLagrangeDiagonal.lean)
-/
@[path]
private lemma needS {R : Type*} [CommRing R] (φ w : PowerSeries R)
  (hw0 : PowerSeries.constantCoeff w = 0) (hw : w = X * φ.subst w) :
  ∀ (N : ℕ) (F : PowerSeries R),
    coeff (N + 1) (F.subst w) + coeff N (F * derivative φ * φ ^ N)
      = coeff (N + 1) (F * φ ^ (N + 1)) := by
  intro N
  induction N with
  | zero =>
    intro F
    set c₀ := coeff 0 F with hc₀
    set F₁ : PowerSeries R := mk fun i => coeff (i + 1) F with hF₁
    have hsplit : F = C c₀ + X * F₁ := by
      ext n; cases n with
      | zero => simp [hc₀]
      | succ m => simp [hF₁, coeff_succ_C, coeff_succ_X_mul, coeff_mk]
    rw [hrec φ w hw0 hw 0 F, ← hF₁, need0 w hw0 (φ * F₁)]
    have hmul0 :
      X * (φ * F₁) + X * (F * derivative φ * φ ^ 0)
        + C c₀ * (φ ^ 0 * (φ - X * derivative φ))
      = F * φ ^ (0 + 1) + X * (X * (F₁ * derivative φ)) := by
      conv_lhs => rw [hsplit]
      conv_rhs => rw [hsplit]
      ring
    have h2 := congrArg (coeff (0 + 1)) hmul0
    simp only [map_add, coeff_succ_X_mul, coeff_zero_X_mul, coeff_C_mul,
      base R φ 0, mul_zero, add_zero] at h2
    linear_combination h2
  | succ k ih =>
    intro F
    set c₀ := coeff 0 F with hc₀
    set F₁ : PowerSeries R := mk fun i => coeff (i + 1) F with hF₁
    have hsplit : F = C c₀ + X * F₁ := by
      ext n; cases n with
      | zero => simp [hc₀]
      | succ m => simp [hF₁, coeff_succ_C, coeff_succ_X_mul, coeff_mk]
    have hih := ih (φ * F₁)
    rw [hrec φ w hw0 hw (k + 1) F, ← hF₁]
    have hmul :
      X * (φ * F₁ * φ ^ (k + 1)) + X * (F * derivative φ * φ ^ (k + 1))
        + C c₀ * (φ ^ (k + 1) * (φ - X * derivative φ))
      = F * φ ^ (k + 1 + 1)
        + X * (X * (φ * F₁ * derivative φ * φ ^ k)) := by
      conv_lhs => rw [hsplit]
      conv_rhs => rw [hsplit]
      ring
    have h2 := congrArg (coeff (k + 1 + 1)) hmul
    simp only [map_add, coeff_succ_X_mul, coeff_C_mul, base R φ (k + 1),
      mul_zero, add_zero] at h2
    linear_combination h2 + hih

end MetaMathlibExt.LagrangeInversionAux

namespace MetaMathlibExt.LagrangeInversionAux

/--
[main](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/HermiteLagrangeDiagonal.lean)
-/
@[path]
any `H` solving `(1 - X·φ'(w))·H = F(w)` has `coeff N H = coeff N (F · φ^N)`. -/
private lemma main {R : Type*} [CommRing R] (φ w : PowerSeries R)
  (hw0 : PowerSeries.constantCoeff w = 0) (hw : w = X * φ.subst w) :
  ∀ (N : ℕ) (F H : PowerSeries R),
    (1 - X * ((derivative φ).subst w)) * H = F.subst w →
    coeff N H = coeff N (F * φ ^ N) := by
  intro N
  induction N with
  | zero =>
    intro F H heq
    rw [pow_zero, mul_one]
    have h0 := congrArg (coeff 0) heq
    rw [need0 w hw0 F] at h0
    rwa [coeff_zero_eq_constantCoeff, map_mul, map_sub, map_one, map_mul,
      constantCoeff_X, zero_mul, sub_zero, one_mul, ← coeff_zero_eq_constantCoeff] at h0
  | succ N ih =>
    intro F H heq
    have hs : HasSubst w := HasSubst.of_constantCoeff_zero' hw0
    have key : coeff (N + 1) H
      = coeff (N + 1) (F.subst w) + coeff N (((derivative φ).subst w) * H) := by
      have h := congrArg (coeff (N + 1)) heq
      have hexp : (1 - X * ((derivative φ).subst w)) * H
        = H - X * (((derivative φ).subst w) * H) := by ring
      rw [hexp, map_sub, coeff_succ_X_mul] at h
      linear_combination h
    have heq' : (1 - X * ((derivative φ).subst w)) * (((derivative φ).subst w) * H)
      = (F * derivative φ).subst w := by
      calc (1 - X * ((derivative φ).subst w)) * (((derivative φ).subst w) * H)
        = ((derivative φ).subst w) * ((1 - X * ((derivative φ).subst w)) * H) := by ring
        _ = ((derivative φ).subst w) * (F.subst w) := by rw [heq]
        _ = (F * derivative φ).subst w := by rw [subst_mul hs]; ring
    have hih := ih (F * derivative φ) (((derivative φ).subst w) * H) heq'
    rw [key, hih]
    have hneed := needS φ w hw0 hw N F
    linear_combination hneed
end MetaMathlibExt.LagrangeInversionAux
section


namespace MetaMathlibExt.LagrangeInversion

/--
[coeff_mul_pow_eq_coeff_of_eq_X_mul_subst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/HermiteLagrangeDiagonal.lean)
-/
@[path]
lemma coeff_mul_pow_eq_coeff_of_eq_X_mul_subst
  [CommRing R]
  {n : ℕ}
  {F phi w G : PowerSeries R}
-- given
  (hw : w = PowerSeries.X * phi.subst w)
  (hG : (1 - PowerSeries.X * (PowerSeries.derivative phi).subst w) * G = F.subst w) :
-- imply
  (PowerSeries.coeff n) (F * phi ^ n) = (PowerSeries.coeff n) G := by
-- proof
  have hw0 : PowerSeries.constantCoeff w = 0 := by
    rw [hw, map_mul, PowerSeries.constantCoeff_X, zero_mul]
  exact (MetaMathlibExt.LagrangeInversionAux.main phi w hw0 hw n F G hG).symm
set_option linter.unusedVariables false in

end MetaMathlibExt.LagrangeInversion

namespace MetaMathlibExt.LagrangeInversion

/--
[hermite_lagrange_diagonal_formula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/HermiteLagrangeDiagonal.lean)
-/
@[path]
lemma hermite_lagrange_diagonal_formula
  [CommRing R]
  {n : ℕ}
  {F phi w G : PowerSeries R}
-- given
  (hw0 : PowerSeries.constantCoeff w = 0)
  (hphi : PowerSeries.coeff 0 phi ≠ 0)
  (hw : w = PowerSeries.X * phi.subst w)
  (hG : (1 - PowerSeries.X * (PowerSeries.derivative phi).subst w) * G = F.subst w) :
-- imply
  (PowerSeries.coeff n) (F * phi ^ n) = (PowerSeries.coeff n) G := by
-- proof
  exact (MetaMathlibExt.LagrangeInversionAux.main phi w hw0 hw n F G hG).symm

end MetaMathlibExt.LagrangeInversion


-- created on 2026-10-20
-- updated on 2026-10-26
