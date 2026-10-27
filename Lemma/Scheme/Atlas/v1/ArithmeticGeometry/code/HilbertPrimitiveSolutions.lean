import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions.Part2
open HilbertSymbol PadicInt in hilbertSymbol
open scoped Classical
open PadicInt HilbertSymbol


/--
[legendreSym_val_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma legendreSym_val_local
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {a : ZMod p} :
-- imply
  legendreSym p (ZMod.val a : ℤ) = (quadraticChar (ZMod p)) a := by
-- proof
  unfold legendreSym
  congr 1
  simp [ZMod.natCast_val]

/--
[padicUnitLegendre_mul_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma padicUnitLegendre_mul_local
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {u₁ u₂ : ℤ_[p]ˣ} :
-- imply
  padicUnitLegendre (u₁ * u₂) = padicUnitLegendre u₁ * padicUnitLegendre u₂ := by
-- proof
  simp only [padicUnitLegendre, legendreSym_val_local]
  rw [show PadicInt.toZMod ((u₁ * u₂ : ℤ_[p]ˣ) : ℤ_[p]) =
    PadicInt.toZMod (u₁ : ℤ_[p]) * PadicInt.toZMod (u₂ : ℤ_[p]) from by
    simp only [Units.val_mul, map_mul]]
  exact map_mul (quadraticChar (ZMod p)) _ _

/--
[padicUnitLegendre_eq_one_or_neg_one_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma padicUnitLegendre_eq_one_or_neg_one_local
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {v : ℤ_[p]ˣ} :
-- imply
  padicUnitLegendre v = 1 ∨ padicUnitLegendre v = -1 := by
-- proof
  simp only [padicUnitLegendre, legendreSym_val_local]
  have hne : PadicInt.toZMod (v : ℤ_[p]) ≠ 0 := by
    intro h
    have hunit : IsUnit (PadicInt.toZMod (v : ℤ_[p])) := IsUnit.map PadicInt.toZMod v.isUnit
    exact not_isUnit_zero (h ▸ hunit)
  exact quadraticChar_dichotomy hne

/--
[padic_unit_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma padic_unit_decomp
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {a : ℚ_[p]ˣ} :
-- imply
  ∃ (α : ℤ) (u : ℤ_[p]ˣ), a = padicPowerUnitZ p α u := by
-- proof
  set v := Padic.valuation (a : ℚ_[p]) with hv_def
  set w : ℚ_[p] := (a : ℚ_[p]) * (p : ℚ_[p]) ^ (-v) with hw_def
  have ha_ne : (a : ℚ_[p]) ≠ 0 := Units.ne_zero a
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.Prime.pos hp.out)
  have hp_ne_zero_real : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
  have hp_ne_zero_qp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp.out)
  have hw_norm : ‖w‖ = 1 := by
    rw [hw_def, norm_mul, Padic.norm_eq_zpow_neg_valuation ha_ne]
    rw [norm_zpow, Padic.norm_p]
    simp only [hv_def]
    rw [inv_zpow, ← zpow_neg, ← zpow_add₀ hp_ne_zero_real]
    simp
  have hw_padic_int : ‖w‖ ≤ 1 := by linarith
  set w_int : ℤ_[p] := ⟨w, hw_padic_int⟩ with hw_int_def
  have hw_unit : IsUnit w_int := by
    rwa [PadicInt.isUnit_iff]
  set u := hw_unit.unit with hu_def
  refine ⟨v, u, ?_⟩
  ext
  simp only [padicPowerUnitZ, Units.val_mul, Units.val_zpow_eq_zpow_val]
  show (a : ℚ_[p]) = ↑(qpPrime p) ^ v * ↑(unitZpToQp u)
  rw [qpPrime, Units.val_mk0, unitZpToQp_coe]
  have hu_eq : (u : ℤ_[p]) = w_int := by simp only [hu_def, IsUnit.unit_spec]
  rw [hu_eq, hw_int_def, Subtype.coe_mk, hw_def]
  rw [zpow_neg]
  field_simp

/--
[natAbs_add_mod_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma natAbs_add_mod_two
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {α₁ α₂ : ℤ} :
-- imply
  (α₁ + α₂).natAbs % 2 = (α₁.natAbs + α₂.natAbs) % 2 := by
-- proof
  have h1 : α₁.natAbs % 2 = (α₁ % 2).natAbs := by omega
  have h2 : α₂.natAbs % 2 = (α₂ % 2).natAbs := by omega
  have h3 : (α₁ + α₂).natAbs % 2 = ((α₁ + α₂) % 2).natAbs := by omega
  rw [h3]
  have h4 : (α₁ + α₂) % 2 = (α₁ % 2 + α₂ % 2) % 2 := by omega
  rw [h4]
  have hm1 : α₁ % 2 = 0 ∨ α₁ % 2 = 1 := by omega
  have hm2 : α₂ % 2 = 0 ∨ α₂ % 2 = 1 := by omega
  obtain h | h <;> rcases hm2 with h' | h' <;> simp [h, h'] <;> omega := hm1

/--
[formula_bilinear_natAbs](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma formula_bilinear_natAbs
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {m : ℕ}
  {α₁ α₂ γ : ℤ}
  {Lu₁ Lu₂ Lw : ℤ}
-- given
  (_hLu₁ : Lu₁ ^ 2 = 1)
  (_hLu₂ : Lu₂ ^ 2 = 1)
  (hLw : Lw ^ 2 = 1) :
-- imply
  (-1 : ℤ) ^ ((α₁ + α₂).natAbs * γ.natAbs * m) * (Lu₁ * Lu₂) ^ γ.natAbs * Lw ^ (α₁ + α₂).natAbs = ((-1 : ℤ) ^ (α₁.natAbs * γ.natAbs * m) * Lu₁ ^ γ.natAbs * Lw ^ α₁.natAbs) * ((-1 : ℤ) ^ (α₂.natAbs * γ.natAbs * m) * Lu₂ ^ γ.natAbs * Lw ^ α₂.natAbs) := by
-- proof
  have neg1_sq : (-1 : ℤ) ^ 2 = 1 := by norm_num
  have hmod_sum : (α₁ + α₂).natAbs % 2 = (α₁.natAbs + α₂.natAbs) % 2 :=
    natAbs_add_mod_two α₁ α₂
  rw [pow_eq_of_sq_eq_one_of_mod_two_eq hLw hmod_sum]
  have hmod_prod : ((α₁ + α₂).natAbs * γ.natAbs * m) % 2 =
    ((α₁.natAbs + α₂.natAbs) * γ.natAbs * m) % 2 := by
    rw [Nat.mul_mod ((α₁ + α₂).natAbs * γ.natAbs),
      Nat.mul_mod ((α₁.natAbs + α₂.natAbs) * γ.natAbs),
      Nat.mul_mod (α₁ + α₂).natAbs,
      Nat.mul_mod (α₁.natAbs + α₂.natAbs), hmod_sum]
  rw [pow_eq_of_sq_eq_one_of_mod_two_eq neg1_sq hmod_prod]
  rw [mul_pow, pow_add Lw]
  have : (α₁.natAbs + α₂.natAbs) * γ.natAbs * m =
    α₁.natAbs * γ.natAbs * m + α₂.natAbs * γ.natAbs * m := by ring
  rw [this, pow_add]
  ring

/--
[padic_unit_square_of_legendre_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma padic_unit_square_of_legendre_one
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {v : ℤ_[p]ˣ}
-- given
  (hp_odd : p ≠ 2)
  (hv : padicUnitLegendre v = 1) :
-- imply
  IsSquare (v : ℤ_[p]) := by
-- proof
  simp only [padicUnitLegendre, legendreSym_val_local] at hv
  have hne : PadicInt.toZMod (v : ℤ_[p]) ≠ 0 :=
    (RingHom.isUnit_map PadicInt.toZMod v.isUnit).ne_zero
  have hIsSquare : IsSquare (PadicInt.toZMod (v : ℤ_[p])) :=
    (quadraticChar_one_iff_isSquare hne).mp hv
  obtain ⟨s, hs⟩ := hIsSquare
  obtain ⟨s_lift, hs_lift⟩ := ZMod.ringHom_surjective PadicInt.toZMod s
  let f : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C (v : ℤ_[p])
  have hval : ‖Polynomial.aeval s_lift f‖ < 1 := by
    have hf_aeval : Polynomial.aeval s_lift f = s_lift ^ 2 - (v : ℤ_[p]) := by
      simp [f, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rw [hf_aeval, norm_lt_one_iff_toZMod_zero, map_sub, map_pow, hs_lift]
    rw [show PadicInt.toZMod (v : ℤ_[p]) = s * s from hs]
    ring
  have hs_unit : IsUnit s_lift := by
    rw [isUnit_iff_toZMod_ne_zero]; intro h0
    have : PadicInt.toZMod (v : ℤ_[p]) = 0 := by
      rw [hs, ← hs_lift, h0]; ring
    exact hne this
  have hderiv : ‖Polynomial.aeval s_lift f.derivative‖ = 1 := by
    have hf_deriv : Polynomial.aeval s_lift f.derivative = 2 * s_lift := by
      simp [f, Polynomial.derivative_sub, Polynomial.derivative_pow,
        Polynomial.derivative_X, Polynomial.derivative_C,
        Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rw [hf_deriv, norm_mul]
    have h2_unit : IsUnit (2 : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff]; by_contra hne2; push Not at hne2
      have hlt2 : ‖(2 : ℤ_[p])‖ < 1 := lt_of_le_of_ne (2 : ℤ_[p]).2 hne2
      rw [PadicInt.norm_lt_one_iff_dvd] at hlt2; obtain ⟨k, hk⟩ := hlt2
      have h1 := congrArg PadicInt.toZMod hk
      simp only [map_ofNat, map_mul] at h1
      rw [toZMod_p_eq_zero, zero_mul] at h1
      have : (2 : ZMod p) ≠ 0 := by
        rw [Ne, show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from by norm_cast,
          ZMod.natCast_eq_zero_iff]; intro hdvd
        exact hp_odd (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) (Nat.Prime.two_le hp.out))
      exact this h1
    rw [PadicInt.isUnit_iff.mp h2_unit, PadicInt.isUnit_iff.mp hs_unit, mul_one]
  obtain ⟨z, hz_root, _⟩ := (hensel_lemma_norm f s_lift hval hderiv).exists
  have hz_sq : z ^ 2 = (v : ℤ_[p]) := by
    have h := hz_root
    simp [f, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at h
    exact sub_eq_zero.mp h
  exact ⟨z, by rw [← hz_sq, sq]⟩

/--
[padicPowerUnitZ_isSquare_of_unit_sq_even_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma padicPowerUnitZ_isSquare_of_unit_sq_even_val
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {v : ℤ_[p]ˣ}
  {k : ℕ}
-- given
  (hv_sq : IsSquare (v : ℤ_[p]))
  (hk : γ.natAbs = k + k) :
-- imply
  IsSquare ((padicPowerUnitZ p γ v : ℚ_[p]ˣ) : ℚ_[p]) := by
-- proof
  obtain ⟨z, hz⟩ := hv_sq
  have hγ_even : Even γ := by
    have : Even γ.natAbs := ⟨k, hk⟩
    rwa [Int.natAbs_even] at this
  obtain ⟨m, hm⟩ := hγ_even
  have hc_val : ((padicPowerUnitZ p γ v : ℚ_[p]ˣ) : ℚ_[p]) =
    ((↑p : ℚ_[p]) ^ m) ^ 2 * ((z : ℚ_[p]) ^ 2) := by
    simp only [padicPowerUnitZ, Units.val_mul, Units.val_zpow_eq_zpow_val]
    rw [qpPrime, Units.val_mk0, hm, unitZpToQp_coe]
    have : (↑p : ℚ_[p]) ^ (m + m) = ((↑p : ℚ_[p]) ^ m) ^ 2 := by
      rw [sq]
      have hp_ne : (↑p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out))
      exact zpow_add₀ hp_ne m m
    rw [this, hz]
    push_cast
    ring
  rw [hc_val]
  exact ⟨(↑p : ℚ_[p]) ^ m * (z : ℚ_[p]), by ring⟩
section TwoAdicBridgeLocal
open PadicInt HilbertSymbol

/--
[hasPrimSolMod8_one_eq_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma hasPrimSolMod8_one_eq_local
  {u v : ℤ_[2]ˣ} :
-- imply
  HasPrimitiveSolutionMod8_one u v ↔ hasPrimSolMod8_one_dec (toZModPow_unit 3 u) (toZModPow_unit 3 v) := by
-- proof
  simp only [HasPrimitiveSolutionMod8_one, hasPrimSolMod8_one_dec, toZModPow_unit_coe]

/--
[hasPrimSolMod8_two_eq_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma hasPrimSolMod8_two_eq_local
  {u v : ℤ_[2]ˣ} :
-- imply
  HasPrimitiveSolutionMod8_two u v ↔ hasPrimSolMod8_two_dec (toZModPow_unit 3 u) (toZModPow_unit 3 v) := by
-- proof
  simp only [HasPrimitiveSolutionMod8_two, hasPrimSolMod8_two_dec, toZModPow_unit_coe]

/--
[hilbert_eq_formula_of_iff_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma hilbert_eq_formula_of_iff_local
  {a b : ℚ_[2]ˣ}
  {solMod : Prop}
  [Decidable solMod]
  {f : ℤ}
-- given
  (h_iff : padicHilbertSymbol 2 a b = 1 ↔ HasPrimitiveSolution a b)
  (h_lift : HasPrimitiveSolution a b ↔ solMod)
  (hf : f = 1 ∨ f = -1)
  (h_formula : solMod ↔ f = 1) :
-- imply
  padicHilbertSymbol 2 a b = f := by
-- proof
  obtain h | h := padicHilbertSymbol.eq_one_or_neg_one a b
  · rw [h]
    obtain hf1 | hf1 := hf
    · exact hf1.symm
    · exfalso
      have hsol : solMod := h_lift.mp (h_iff.mp h)
      rw [h_formula.mp hsol] at hf1; exact absurd hf1 (by omega)
  · rw [h]
    obtain hf1 | hf1 := hf
    · exfalso
      have hf1' : f = 1 := hf1
      rw [← h_formula] at hf1'
      have := h_lift.mpr hf1'
      rw [← h_iff] at this
      rw [this] at h; exact absurd h (by omega)
    · exact hf1.symm

/--
[thm_10_9_one_one_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma thm_10_9_one_one_local
  {u v : ℤ_[2]ˣ} :
-- imply
  padicHilbertSymbol 2 (padicUnit_one u) (padicUnit_one v) = hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) 0 0 :=
-- proof
  hilbert_eq_formula_of_iff_local
    (hilbert_eq_one_iff_hasPrimitiveSolution (padicUnit_one u) (padicUnit_one v))
    ((lemma_10_8_one u v).trans (hasPrimSolMod8_one_eq_local u v))
    (formula_eq_one_or_neg_one _ _ 0 0)
    (formula_one_one_verified _ _)

/--
[thm_10_9_two_one_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma thm_10_9_two_one_local
  {u v : ℤ_[2]ˣ} :
-- imply
  padicHilbertSymbol 2 (padicUnit_two u) (padicUnit_one v) = hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) 1 0 :=
-- proof
  hilbert_eq_formula_of_iff_local
    (hilbert_eq_one_iff_hasPrimitiveSolution (padicUnit_two u) (padicUnit_one v))
    ((lemma_10_8_two u v).trans (hasPrimSolMod8_two_eq_local u v))
    (formula_eq_one_or_neg_one _ _ 1 0)
    (formula_two_one_verified _ _)

/--
[hilbertSymbol_symm_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma hilbertSymbol_symm_local
  {a b : ℚ_[2]ˣ} :
-- imply
  hilbertSymbol ℚ_[2] a b = hilbertSymbol ℚ_[2] b a := by
-- proof
  unfold hilbertSymbol
  have h : HilbertSymbol.IsSolvable ℚ_[2] a b ↔ HilbertSymbol.IsSolvable ℚ_[2] b a := by
    constructor
    · rintro ⟨x, y, h⟩; exact ⟨y, x, by rw [add_comm]; exact h⟩
    · rintro ⟨x, y, h⟩; exact ⟨y, x, by rw [add_comm]; exact h⟩
  simp_rw [show HilbertSymbol.IsSolvable ℚ_[2] a b = HilbertSymbol.IsSolvable ℚ_[2] b a from propext h]

/--
[thm_10_9_one_two_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma thm_10_9_one_two_local
  {u v : ℤ_[2]ˣ} :
-- imply
  padicHilbertSymbol 2 (padicUnit_one u) (padicUnit_two v) = hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) 0 1 := by
-- proof
  rw [show padicHilbertSymbol 2 (padicUnit_one u) (padicUnit_two v) =
    padicHilbertSymbol 2 (padicUnit_two v) (padicUnit_one u) from
    hilbertSymbol_symm_local _ _]
  exact hilbert_eq_formula_of_iff_local
    (hilbert_eq_one_iff_hasPrimitiveSolution (padicUnit_two v) (padicUnit_one u))
    ((lemma_10_8_two v u).trans (hasPrimSolMod8_two_eq_local v u))
    (formula_eq_one_or_neg_one _ _ 0 1)
    (formula_one_two_verified _ _)

/--
[toZModPow_unit_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma toZModPow_unit_mul
  {u v : ℤ_[2]ˣ} :
-- imply
  toZModPow_unit 3 (u * v) = toZModPow_unit 3 u * toZModPow_unit 3 v := by
-- proof
  ext
  simp only [toZModPow_unit_coe, Units.val_mul, map_mul]
/-- Theorem 10.9, case $(\alpha,\beta) = (1,1)$: $(2u, 2v)_{\mathbb{Q}_2}$ equals the
closed-form formula at $(1, 1)$. This is the remaining case completing Theorem 10.9. -/
end TwoAdicBridgeLocal
open HilbertSymbol PadicInt in
/-- Half of bilinearity over $\mathbb{Q}_2$: if $(a, c)_{\mathbb{Q}_2} = (b, c)_{\mathbb{Q}_2} = -1$,
then $(ab, c)_{\mathbb{Q}_2} = 1$. Reduced via the $p$-adic decomposition and the closed-form
formula to the verified bilinearity lemma `formula_mul_left_core`. -/
section Nondeg2Adic_Computational
attribute [-instance] Classical.propDecidable
/-- Local copy (within this `Nondeg2Adic_Computational` section, with classical decidability
disabled) of the decidable predicate for primitive mod-$8$ solvability of
$z^2 = u_0 x^2 + v_0 y^2$. -/
@[reducible] def hasPrimSolMod8_one_loc (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  ∃ x₀ y₀ z₀ : ZMod (2 ^ 3),
    (IsUnit x₀ ∨ IsUnit y₀ ∨ IsUnit z₀) ∧
    z₀ ^ 2 = (↑u₀ : ZMod (2 ^ 3)) * x₀ ^ 2 + (↑v₀ : ZMod (2 ^ 3)) * y₀ ^ 2
/-- Local copy (within `Nondeg2Adic_Computational`) of the decidable predicate for primitive
mod-$8$ solvability of $z^2 = 2 u_0 x^2 + v_0 y^2$. -/
@[reducible] def hasPrimSolMod8_two_loc (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  ∃ x₀ y₀ z₀ : ZMod (2 ^ 3),
    (IsUnit x₀ ∨ IsUnit y₀ ∨ IsUnit z₀) ∧
    z₀ ^ 2 = (2 : ZMod (2 ^ 3)) * (↑u₀ : ZMod (2 ^ 3)) * x₀ ^ 2 +
      (↑v₀ : ZMod (2 ^ 3)) * y₀ ^ 2

/--
[nondeg_mod8_unit_witness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma nondeg_mod8_unit_witness
-- imply
  ∀ (w₀ : (ZMod (2 ^ 3))ˣ), w₀ ≠ 1 → nondeg_unit_combined w₀ := by
-- proof
  native_decide
/-- Decidable predicate: a unit $w_0 \in (\mathbb{Z}/8)^\times$ admits some unit $v_0$ for
which $z^2 = 2 w_0 x^2 + v_0 y^2$ is insolvable mod $8$. Used for nondegeneracy when the
valuation of $c$ is odd. -/
@[reducible] def nondeg_two_prop (w₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  ∃ (v₀ : (ZMod (2 ^ 3))ˣ), ¬ hasPrimSolMod8_two_loc w₀ v₀

/--
[nondeg_mod8_two_witness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma nondeg_mod8_two_witness
-- imply
  ∀ (w₀ : (ZMod (2 ^ 3))ˣ), nondeg_two_prop w₀ := by
-- proof
  native_decide
end Nondeg2Adic_Computational
open HilbertSymbol

/--
[toZMod8Unit_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma toZMod8Unit_val
  {w : ℤ_[2]ˣ} :
-- imply
  (↑(toZMod8Unit w) : ZMod (2 ^ 3)) = PadicInt.toZModPow 3 (↑w : ℤ_[2]) :=
-- proof
  IsUnit.unit_spec _

/--
[hasPrimSolMod8_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma hasPrimSolMod8_one_iff
  {u v : ℤ_[2]ˣ} :
-- imply
  HasPrimitiveSolutionMod8_one u v ↔ hasPrimSolMod8_one_loc (toZMod8Unit u) (toZMod8Unit v) := by
-- proof
  simp only [HasPrimitiveSolutionMod8_one, hasPrimSolMod8_one_loc, toZMod8Unit_val]

/--
[hasPrimSolMod8_two_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma hasPrimSolMod8_two_iff
  {u v : ℤ_[2]ˣ} :
-- imply
  HasPrimitiveSolutionMod8_two u v ↔ hasPrimSolMod8_two_loc (toZMod8Unit u) (toZMod8Unit v) := by
-- proof
  simp only [HasPrimitiveSolutionMod8_two, hasPrimSolMod8_two_loc, toZMod8Unit_val]

/--
[toZMod8Unit_surj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma toZMod8Unit_surj
  {u₀ : (ZMod (2 ^ 3))ˣ} :
-- imply
  ∃ u : ℤ_[2]ˣ, toZMod8Unit u = u₀ := by
-- proof
  obtain ⟨x, hx⟩ := PadicInt.toZModPow_surjective' 3 (↑u₀ : ZMod (2 ^ 3))
  have hxu : IsUnit x := (PadicInt.isUnit_toZModPow_iff (show 0 < 3 from by omega)).mp
    (hx ▸ u₀.isUnit)
  refine ⟨hxu.unit, ?_⟩
  ext
  simp only [toZMod8Unit_val, IsUnit.unit_spec]
  exact hx

/--
[padicUnit_one_eq_unitZpToQp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma padicUnit_one_eq_unitZpToQp
  {w : ℤ_[2]ˣ} :
-- imply
  (padicUnit_one w : ℚ_[2]) = (unitZpToQp w : ℚ_[2]) := by
-- proof
  simp [padicUnit_one_val, unitZpToQp_coe]

/--
[padicUnit_one_eq_unitZpToQp'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma padicUnit_one_eq_unitZpToQp'
  {w : ℤ_[2]ˣ} :
-- imply
  padicUnit_one w = unitZpToQp w := by
-- proof
  ext; exact padicUnit_one_eq_unitZpToQp w

/--
[padicUnit_two_eq_qpPrime_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma padicUnit_two_eq_qpPrime_mul
  {w : ℤ_[2]ˣ} :
-- imply
  (padicUnit_two w : ℚ_[2]) = (qpPrime 2 : ℚ_[2]) * (unitZpToQp w : ℚ_[2]) := by
-- proof
  simp [padicUnit_two_val, unitZpToQp_coe, qpPrime, Units.val_mk0]

/--
[padicUnit_two_eq_qpPrime_mul'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma padicUnit_two_eq_qpPrime_mul'
  {w : ℤ_[2]ˣ} :
-- imply
  padicUnit_two w = qpPrime 2 * unitZpToQp w := by
-- proof
  ext; exact padicUnit_two_eq_qpPrime_mul w

/--
[padic_nondegenerate_p2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma padic_nondegenerate_p2
  [hp : Fact (Nat.Prime 2)] :
-- imply
  ∀ (c : ℚ_[2]ˣ), ¬ IsSquare (c : ℚ_[2]) → ∃ b : ℚ_[2]ˣ, hilbertSymbol ℚ_[2] b c = -1 := by
-- proof
  intro c hc
  obtain ⟨γ, w, hc_eq⟩ := padic_unit_decomp c
  obtain ⟨m, hm⟩ | ⟨m, hm⟩ := Int.even_or_odd γ
  ·
    have hc_sq : c = (qpPrime 2) ^ m * (qpPrime 2) ^ m * unitZpToQp w := by
      rw [hc_eq, padicPowerUnitZ, hm]; group
    have huw_nsq : ¬ IsSquare ((unitZpToQp w : ℚ_[2]ˣ) : ℚ_[2]) := by
      intro ⟨s, hs⟩
      apply hc
      refine ⟨(qpPrime 2) ^ m * s, ?_⟩
      rw [hc_sq]; simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      rw [hs]; push_cast; ring
    have hw_ne_one : toZMod8Unit w ≠ 1 := by
      intro h
      apply huw_nsq
      have hmod : PadicInt.toZModPow 3 (↑w : ℤ_[2]) = 1 := by
        rw [← toZMod8Unit_val, h]; simp
      have hdvd : (2 : ℤ_[2]) ^ 3 ∣ 1 * 1 ^ 2 - (↑w : ℤ_[2]) := by
        rw [one_mul, one_pow]
        rw [show (2 : ℤ_[2]) ^ 3 = ((2 : ℕ) : ℤ_[2]) ^ 3 from by norm_cast]
        rw [← PadicInt.toZModPow_eq_zero_iff_dvd]
        simp only [map_sub, map_one, hmod, sub_self]
      obtain ⟨z', hz', _⟩ := exists_mul_sq_eq_of_mod8 isUnit_one isUnit_one hdvd
      rw [one_mul] at hz'
      refine ⟨(z' : ℚ_[2]), ?_⟩
      rw [unitZpToQp_coe]
      have hsq : (↑w : ℤ_[2]) = z' * z' := by rw [← sq]; exact hz'.symm
      have := congr_arg (Subtype.val : ℤ_[2] → ℚ_[2]) hsq
      push_cast at this ⊢; exact this
    obtain hw_wit := nondeg_mod8_unit_witness (toZMod8Unit w) hw_ne_one
    obtain ⟨v₀, hv₀⟩ | ⟨v₀, hv₀⟩ := hw_wit
    ·
      obtain ⟨v, hv_eq⟩ := toZMod8Unit_surj v₀
      refine ⟨padicUnit_one v, ?_⟩
      have hc_rw : c = (qpPrime 2 ^ m) ^ 2 * padicUnit_one w := by
        rw [hc_sq, padicUnit_one_eq_unitZpToQp']; group
      rw [hc_rw, hilbert_sq_mul_right]
      rw [hilbertSymbol.eq_neg_one_iff]
      intro hsol
      apply hv₀
      rw [← hv_eq, ← hasPrimSolMod8_one_iff]
      exact (lemma_10_8_one v w).mp
        ((isSolvable_iff_hasPrimitiveSolution _ _).mp
          (by rwa [padicUnit_one_eq_unitZpToQp'] at hsol))
    ·
      obtain ⟨v, hv_eq⟩ := toZMod8Unit_surj v₀
      refine ⟨padicUnit_two v, ?_⟩
      have hc_rw : c = (qpPrime 2 ^ m) ^ 2 * padicUnit_one w := by
        rw [hc_sq, padicUnit_one_eq_unitZpToQp']; group
      rw [hc_rw, hilbert_sq_mul_right]
      rw [hilbertSymbol.eq_neg_one_iff]
      intro hsol
      apply hv₀
      rw [← hv_eq, ← hasPrimSolMod8_two_iff]
      exact (lemma_10_8_two v w).mp
        ((isSolvable_iff_hasPrimitiveSolution _ _).mp
          (by rwa [padicUnit_one_eq_unitZpToQp'] at hsol))
  ·
    have hc_sq : c = (qpPrime 2) ^ m * (qpPrime 2) ^ m *
      (qpPrime 2 * unitZpToQp w) := by
      rw [hc_eq, padicPowerUnitZ, hm]; group
    obtain ⟨v₀, hv₀⟩ := nondeg_mod8_two_witness (toZMod8Unit w)
    obtain ⟨v, hv_eq⟩ := toZMod8Unit_surj v₀
    refine ⟨padicUnit_one v, ?_⟩
    have hc_rw : c = (qpPrime 2 ^ m) ^ 2 * padicUnit_two w := by
      rw [hc_sq, padicUnit_two_eq_qpPrime_mul']; group
    rw [hc_rw, hilbert_sq_mul_right]
    rw [hilbert_symm]
    rw [hilbertSymbol.eq_neg_one_iff]
    intro hsol
    apply hv₀
    rw [← hv_eq, ← hasPrimSolMod8_two_iff]
    exact (lemma_10_8_two w v).mp
      ((isSolvable_iff_hasPrimitiveSolution _ _).mp hsol)

/--
[padic_nondegenerate_ax](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma padic_nondegenerate_ax
  {p : ℕ}
  [Fact p.Prime] :
-- imply
  ∀ (c : ℚ_[p]ˣ), ¬ IsSquare (c : ℚ_[p]) → ∃ b : ℚ_[p]ˣ, hilbertSymbol ℚ_[p] b c = -1 := by
-- proof
  by_cases hp2 : p = 2
  · subst hp2; exact padic_nondegenerate_p2
  · intro c hc
    obtain ⟨γ, w, hc_eq⟩ := padic_unit_decomp c
    have hrc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact_mod_cast hp2
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hrc
    have ha_ne : a ≠ 0 := by intro h; rw [h, MulChar.map_zero] at ha; exact absurd ha (by norm_num)
    obtain ⟨x, hx⟩ := ZMod.ringHom_surjective PadicInt.toZMod a
    have hx_unit : IsUnit x := (isUnit_iff_toZMod_ne_zero x).mpr (hx ▸ ha_ne)
    set u_nr := hx_unit.unit with hu_nr_def
    have hL_nr : padicUnitLegendre u_nr = -1 := by
      simp only [padicUnitLegendre, legendreSym_val_local]
      rw [show (u_nr : ℤ_[p]) = x from IsUnit.unit_spec hx_unit]
      rwa [hx]
    obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Nat.even_or_odd γ.natAbs
    ·
      have hLw : padicUnitLegendre w = -1 := by
        obtain hLw | hLw := padicUnitLegendre_eq_one_or_neg_one_local w
        ·
          exfalso; apply hc
          have hw_sq := padic_unit_square_of_legendre_one hp2 w hLw
          rw [hc_eq, show ((padicPowerUnitZ p γ w : ℚ_[p]ˣ) : ℚ_[p]) =
            ((padicPowerUnitZ p γ w : ℚ_[p]ˣ) : ℚ_[p]) from rfl]
          exact padicPowerUnitZ_isSquare_of_unit_sq_even_val w hw_sq k hk
        · exact hLw
      refine ⟨padicPowerUnitZ p 1 1, ?_⟩
      rw [hc_eq]
      change padicHilbertSymbol p _ _ = -1
      rw [hilbert_formula_odd_general hp2]
      have hL1 : padicUnitLegendre (1 : ℤ_[p]ˣ) = 1 := by
        simp only [padicUnitLegendre, Units.val_one, map_one, ZMod.val_one p]
        exact legendreSym.at_one p
      simp only [Int.natAbs_one]
      rw [hk, hL1, hLw]
      simp only [one_pow, mul_one, pow_one]
      have : 1 * (k + k) * ((p - 1) / 2) = 2 * (k * ((p - 1) / 2)) := by ring
      rw [this, pow_mul, neg_one_sq, one_pow]
      norm_num
    ·
      refine ⟨padicPowerUnitZ p 0 u_nr, ?_⟩
      rw [hc_eq]
      change padicHilbertSymbol p _ _ = -1
      rw [hilbert_formula_odd_general hp2]
      simp only [Int.natAbs_zero, zero_mul, pow_zero, mul_one, one_mul]
      rw [hL_nr, hk]
      simp [pow_succ, pow_mul]

/--
[real_hilbert_neg_one_imp_neg_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma real_hilbert_neg_one_imp_neg_right
  {a c : ℝˣ}
-- given
  (h : hilbertSymbol ℝ a c = -1) :
-- imply
  (c : ℝ) < 0 := by
-- proof
  by_contra hc
  push Not at hc
  have hpos : 0 < (c : ℝ) := lt_of_le_of_ne hc (Ne.symm c.ne_zero)
  rw [hilbertSymbol.eq_neg_one_iff] at h
  apply h
  refine ⟨0, 1 / Real.sqrt c, ?_⟩
  simp only [mul_zero, sq (0 : ℝ), zero_add]
  rw [div_pow, one_pow, Real.sq_sqrt hpos.le]
  field_simp

namespace hilbertSymbol

/--
[symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma symm
  [Field F]
  {a b : Fˣ} :
-- imply
  hilbertSymbol F a b = hilbertSymbol F b a := by
-- proof
  unfold hilbertSymbol
  have h : HilbertSymbol.IsSolvable F a b ↔ HilbertSymbol.IsSolvable F b a := by
    constructor
    · rintro ⟨x, y, h⟩
      exact ⟨y, x, by rw [add_comm]; exact h⟩
    · rintro ⟨x, y, h⟩
      exact ⟨y, x, by rw [add_comm]; exact h⟩
  simp_rw [show HilbertSymbol.IsSolvable F a b = HilbertSymbol.IsSolvable F b a from propext h]

end hilbertSymbol

namespace hilbertSymbol

/--
[mul_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma mul_left
  [Field F]
  [HilbertBilinearField F]
  {a b c : Fˣ} :
-- imply
  hilbertSymbol F (a * b) c = hilbertSymbol F a c * hilbertSymbol F b c := by
-- proof
  obtain hac | hac := eq_one_or_neg_one a c
  · exact (hilbert_mul_of_eq_one a b c hac).symm
  · rcases eq_one_or_neg_one b c with hbc | hbc
    · rw [show a * b = b * a from mul_comm a b]
      have key := (hilbert_mul_of_eq_one b a c hbc).symm
      rw [key, hbc, one_mul]; ring
    · rw [isSolvable_mul_of_both_neg a b c hac hbc, hac, hbc]; norm_num

end hilbertSymbol

namespace hilbertSymbol

/--
[mul_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
lemma mul_right
  [Field F]
  [HilbertBilinearField F]
  {a b c : Fˣ} :
-- imply
  hilbertSymbol F a (b * c) = hilbertSymbol F a b * hilbertSymbol F a c := by
-- proof
  rw [symm a (b * c), mul_left, symm b a, symm c a]

end hilbertSymbol

/--
[real_unit_not_square_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
private lemma real_unit_not_square_neg_eq
  {c : ℝˣ}
-- given
  (hc : ¬ IsSquare (c : ℝ)) :
-- imply
  (c : ℝ) < 0 := by
-- proof
  apply real_unit_not_square_neg c hc

/--
[real_pos_isSolvable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
private lemma real_pos_isSolvable_eq
  {a : ℝˣ}
  {b : ℝˣ}
-- given
  (ha : 0 < (a : ℝ)) :
-- imply
  HilbertSymbol.IsSolvable ℝ a b := by
-- proof
  apply real_pos_isSolvable a ha b

/--
[real_hilbert_neg_one_imp_neg_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
private lemma real_hilbert_neg_one_imp_neg_left_eq
  {a c : ℝˣ}
-- given
  (h : hilbertSymbol ℝ a c = -1) :
-- imply
  (a : ℝ) < 0 := by
-- proof
  apply real_hilbert_neg_one_imp_neg_left a c h

/--
[isSolvable_mul_of_both_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
private lemma isSolvable_mul_of_both_neg_eq
  [Field F]
  [HilbertBilinearField F]
  {a b c : Fˣ}
-- given
  (ha : hilbertSymbol F a c = -1)
  (hb : hilbertSymbol F b c = -1) :
-- imply
  hilbertSymbol F (a * b) c = 1 := by
-- proof
  apply hilbertSymbol.isSolvable_mul_of_both_neg a b c ha hb

/--
[nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean)
-/
@[path]
private lemma nondegenerate_eq
  [Field F]
  [HilbertBilinearField F]
  {c : Fˣ}
-- given
  (hc : ¬ IsSquare (c : F)) :
-- imply
  ∃ b : Fˣ, hilbertSymbol F b c = -1 := by
-- proof
  apply hilbertSymbol.nondegenerate c hc


-- created on 2026-10-23
