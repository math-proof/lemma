import Lemma.Matrix.RothAuxCombination1.eq.Zero.of.EqMulVecRothAuxMatrix_0.RothCoeff.IsAlgebraic
open MathlibExt.NumberTheory.RothAuxiliary
open Matrix
open scoped Matrix BigOperators Polynomial nonZeroDivisors


private lemma intPolynomial_ne_zero
  {α : ℝ}
-- given
  (hα : IsAlgebraic ℚ α) :
-- imply
  rothIntPolynomial α ≠ 0 := by
-- proof
  obtain ⟨b, hb, hspec⟩ :=
    IsLocalization.integerNormalization_spec ℤ⁰ (minpoly ℚ α)
  intro hf
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbQ : algebraMap ℤ ℚ b ≠ 0 := Int.cast_ne_zero.mpr hb0
  have hsmul : b • minpoly ℚ α ≠ 0 := by
    rw [Algebra.smul_def]
    apply mul_ne_zero (Polynomial.C_ne_zero.mpr hbQ) (minpoly.ne_zero hα.isIntegral)
  apply hsmul
  change IsLocalization.integerNormalization ℤ⁰ (minpoly ℚ α) = 0 at hf
  rw [← hspec, hf, Polynomial.map_zero]

private lemma intPolynomial_isRoot
  (α : ℝ) :
-- imply
  Polynomial.eval α ((rothIntPolynomial α).map (algebraMap ℤ ℝ)) = 0 := by
-- proof
  obtain ⟨b, hb, hspec⟩ :=
    IsLocalization.integerNormalization_spec ℤ⁰ (minpoly ℚ α)
  change Polynomial.eval α
    ((IsLocalization.integerNormalization ℤ⁰ (minpoly ℚ α)).map
      (algebraMap ℤ ℝ)) = 0
  have hmap : algebraMap ℤ ℝ = (algebraMap ℚ ℝ).comp (algebraMap ℤ ℚ) := by
    ext
    simp
  have hmapsmul :
      Polynomial.map (algebraMap ℚ ℝ) (b • minpoly ℚ α) =
        b • Polynomial.map (algebraMap ℚ ℝ) (minpoly ℚ α) :=
    map_zsmul (Polynomial.mapRingHom (algebraMap ℚ ℝ)) b (minpoly ℚ α)
  have hroot : Polynomial.eval₂ (algebraMap ℚ ℝ) α (minpoly ℚ α) = 0 := by
    rw [← Polynomial.aeval_def]
    apply minpoly.aeval ℚ α
  rw [hmap, ← Polynomial.map_map, hspec, hmapsmul, Polynomial.eval_smul]
  simp [Polynomial.eval_map, hroot]

private lemma intPolynomial_natDegree_pos
  {α : ℝ}
-- given
  (hα : IsAlgebraic ℚ α) :
-- imply
  0 < (rothIntPolynomial α).natDegree := by
-- proof
  let f := rothIntPolynomial α
  have hf : f ≠ 0 := intPolynomial_ne_zero hα
  by_contra hnot
  have hd : f.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
  have hfC : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd
  have hr := intPolynomial_isRoot α
  change Polynomial.eval α (f.map (algebraMap ℤ ℝ)) = 0 at hr
  rw [hfC, Polynomial.map_C, Polynomial.eval_C] at hr
  have hc : f.coeff 0 = 0 := Int.cast_eq_zero.mp hr
  apply hf
  rw [hfC, hc, Polynomial.C_0]

private lemma integralPolynomial_isRoot
  (α : ℝ)
-- given
  (hα : IsAlgebraic ℚ α) :
-- imply
  Polynomial.eval₂ (algebraMap ℤ ℝ)
      (((rothIntPolynomial α).leadingCoeff : ℝ) * α)
      (rothIntegralPolynomial α) = 0 := by
-- proof
  let f := rothIntPolynomial α
  have hd : 1 ≤ f.natDegree := intPolynomial_natDegree_pos hα
  have hfroot : Polynomial.eval₂ (algebraMap ℤ ℝ) α f = 0 := by
    simpa [f, Polynomial.eval_map] using intPolynomial_isRoot α
  change Polynomial.eval₂ (algebraMap ℤ ℝ) ((f.leadingCoeff : ℝ) * α)
    f.integralNormalization = 0
  calc
    _ = (algebraMap ℤ ℝ f.leadingCoeff) ^ (f.natDegree - 1) *
        Polynomial.eval₂ (algebraMap ℤ ℝ) α f := by
      simpa using
        Polynomial.integralNormalization_eval₂_leadingCoeff_mul hd
          (algebraMap ℤ ℝ) α
    _ = 0 := by rw [hfroot, mul_zero]

private lemma powerCoord_eval₂
  [CommRing R]
  (f : ℤ →+* R)
  (g : ℤ[X])
  (β : R)
-- given
  (hroot : Polynomial.eval₂ f β g = 0)
  (n : ℕ) :
-- imply
  Polynomial.eval₂ f β (rothPowerCoord g n) = β ^ n := by
-- proof
  induction n with
  | zero => simp [rothPowerCoord]
  | succ n ih =>
    simp [rothPowerCoord, ih, hroot, pow_succ']

private lemma termDegree_le
  {m : ℕ}
  {r : Fin m → ℕ}
  (i j : RothBox r) :
-- imply
  rothTermDegree i j ≤ ∑ h, r h := by
-- proof
  unfold rothTermDegree
  gcongr with h
  apply (Nat.sub_le _ _).trans (Nat.le_of_lt_succ (j h).isLt)

private lemma scaledPowerCoord_eval
  (α : ℝ)
  {S n : ℕ}
-- given
  (hα : IsAlgebraic ℚ α)
  (hn : n ≤ S) :
-- imply
  Polynomial.eval₂ (algebraMap ℤ ℝ)
      (((rothIntPolynomial α).leadingCoeff : ℝ) * α)
      (rothScaledPowerCoord α S n) =
    ((rothIntPolynomial α).leadingCoeff : ℝ) ^ S * α ^ n := by
-- proof
  let a := (rothIntPolynomial α).leadingCoeff
  rw [rothScaledPowerCoord, Polynomial.eval₂_mul, Polynomial.eval₂_C]
  have hpow := powerCoord_eval₂ (algebraMap ℤ ℝ) (rothIntegralPolynomial α)
    (((rothIntPolynomial α).leadingCoeff : ℝ) * α)
    (integralPolynomial_isRoot α hα) n
  rw [hpow]
  change ((a ^ (S - n) : ℤ) : ℝ) * (((a : ℝ) * α) ^ n) = _
  push_cast
  rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]

private lemma auxTerm_eval
  (α : ℝ)
  {m : ℕ}
  {r : Fin m → ℕ}
  (i j : RothBox r)
-- given
  (hα : IsAlgebraic ℚ α) :
-- imply
  Polynomial.eval₂ (algebraMap ℤ ℝ)
      (((rothIntPolynomial α).leadingCoeff : ℝ) * α)
      (rothAuxTerm α i j) =
    (∏ h, (Nat.choose (j h) (i h) : ℝ)) *
      ((rothIntPolynomial α).leadingCoeff : ℝ) ^ (∑ h, r h) *
        α ^ rothTermDegree i j := by
-- proof
  let S := ∑ h, r h
  have hn : rothTermDegree i j ≤ S := termDegree_le i j
  rw [rothAuxTerm, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    scaledPowerCoord_eval α hα hn]
  rw [map_prod]
  rw [algebraMap_int_eq, Int.coe_castRingHom]
  dsimp only
  simp only [Int.cast_natCast]
  dsimp [S]
  ring

private lemma auxCombination_eval
  (α : ℝ)
  {m : ℕ}
  {r : Fin m → ℕ}
  (i : RothBox r)
  (c : RothCoeff r)
-- given
  (hα : IsAlgebraic ℚ α) :
-- imply
  Polynomial.eval₂ (algebraMap ℤ ℝ)
      (((rothIntPolynomial α).leadingCoeff : ℝ) * α)
      (rothAuxCombination α i c) =
    ((rothIntPolynomial α).leadingCoeff : ℝ) ^ (∑ h, r h) *
      rothHasseEval c (fun h ↦ i h) (fun _ ↦ α) := by
-- proof
  rw [rothAuxCombination, Polynomial.eval₂_finsetSum]
  unfold rothHasseEval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C]
  rw [auxTerm_eval α i j hα]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [algebraMap_int_eq, Int.coe_castRingHom]
  dsimp only
  simp only [rothTermDegree]
  ring

/--
[rothHasseEval_eq_zero_of_mulVec_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {α : ℝ}
  {m : ℕ}
  {r : Fin m → ℕ}
  {γ : ℝ}
  {i : RothLowIndex r γ}
  {c : RothCoeff r}
-- given
  (hα : IsAlgebraic ℚ α)
  (hker : Matrix.mulVec (rothAuxMatrix α r γ) c = 0) :
-- imply
  rothHasseEval c (fun h ↦ i.1 h) (fun _ ↦ α) = 0 := by
-- proof
  have hcomb := RothAuxCombination1.eq.Zero.of.EqMulVecRothAuxMatrix_0.RothCoeff.IsAlgebraic (i := i) hα hker
  have heval := auxCombination_eval α i.1 c hα
  rw [hcomb, Polynomial.eval₂_zero] at heval
  have ha : (rothIntPolynomial α).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (intPolynomial_ne_zero hα)
  apply (mul_eq_zero.mp heval.symm).resolve_left
  apply pow_ne_zero
  exact_mod_cast ha


-- created on 2026-10-21
