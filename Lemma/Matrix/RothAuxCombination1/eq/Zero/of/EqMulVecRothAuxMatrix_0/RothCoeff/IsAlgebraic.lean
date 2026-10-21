import sympy.atlas.NumberTheory.RothAuxiliary
import sympy.Basic
open MathlibExt.NumberTheory.RothAuxiliary
open scoped Matrix BigOperators Polynomial nonZeroDivisors


private lemma degree_C_mul_lt
  {P : ℤ[X]}
  {d : ℕ}
-- given
  (hP : P.degree < d)
  (c : ℤ) :
-- imply
  (Polynomial.C c * P).degree < d := by
-- proof
  if hc : c = 0 then
    simp [hc]
  else
    rw [Polynomial.degree_C_mul hc]
    apply hP

private lemma powerCoord_degree_lt
  {g : ℤ[X]}
-- given
  (hg : g.Monic)
  (hd : 0 < g.natDegree)
  (n : ℕ) :
-- imply
  (rothPowerCoord g n).degree < g.natDegree := by
-- proof
  induction n with
  | zero =>
    rw [rothPowerCoord, Polynomial.degree_one]
    apply WithBot.coe_pos.mpr hd
  | succ n ih =>
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro k hk
    cases k with
    | zero => omega
    | succ k =>
      rw [rothPowerCoord, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
        Polynomial.coeff_C_mul]
      if heq : k + 1 = g.natDegree then
        have hkpred : k = g.natDegree - 1 := by omega
        have hdsub : g.natDegree - 1 + 1 = g.natDegree := by omega
        rw [hkpred, hdsub, hg.coeff_natDegree]
        ring
      else
        have hgt : g.natDegree < k + 1 := lt_of_le_of_ne hk (Ne.symm heq)
        have hku : g.natDegree ≤ k := by omega
        rw [(Polynomial.degree_lt_iff_coeff_zero _ _).mp ih k hku,
          Polynomial.coeff_eq_zero_of_natDegree_lt hgt]
        ring

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

private lemma auxTerm_degree_lt
  (α : ℝ)
  {m : ℕ}
  {r : Fin m → ℕ}
  (i j : RothBox r)
-- given
  (hα : IsAlgebraic ℚ α) :
-- imply
  (rothAuxTerm α i j).degree < (rothIntegralPolynomial α).natDegree := by
-- proof
  unfold rothAuxTerm rothScaledPowerCoord
  apply degree_C_mul_lt
  apply degree_C_mul_lt
  apply powerCoord_degree_lt
  ·
    apply Polynomial.monic_integralNormalization (intPolynomial_ne_zero hα)
  ·
    simpa [rothIntegralPolynomial] using intPolynomial_natDegree_pos hα

/--
[rothAuxCombination_eq_zero_of_mulVec_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
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
  rothAuxCombination α i.1 c = 0 := by
-- proof
  ext k
  change (rothAuxCombination α i.1 c).coeff k = 0
  have hcoeff_sum :
      (rothAuxCombination α i.1 c).coeff k =
        ∑ j, (rothAuxTerm α i.1 j).coeff k * c j := by
    classical
    rw [rothAuxCombination, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro j _
    rw [Polynomial.coeff_C_mul]
    ring
  rw [hcoeff_sum]
  if hk : k < (rothIntegralPolynomial α).natDegree then
    let k' : Fin (rothIntegralPolynomial α).natDegree := ⟨k, hk⟩
    have hrow := congrFun hker (i, k')
    change Matrix.mulVec (rothAuxMatrix α r γ) c (i, k') = 0 at hrow
    simpa [Matrix.mulVec, dotProduct, rothAuxMatrix, k'] using hrow
  else
    apply Finset.sum_eq_zero
    intro j _
    have hdegree := auxTerm_degree_lt α i.1 j hα
    have hcoeff : (rothAuxTerm α i.1 j).coeff k = 0 :=
      (Polynomial.degree_lt_iff_coeff_zero _ _).mp hdegree k (Nat.le_of_not_gt hk)
    rw [hcoeff, zero_mul]



-- created on 2026-10-21




-- created on 2026-10-21
