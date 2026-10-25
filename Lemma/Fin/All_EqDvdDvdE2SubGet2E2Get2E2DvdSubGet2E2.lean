import Mathlib
import sympy.Basic
import Lemma.ModularForm.HeckeOperator
open UpperHalfPlane Matrix MatrixGroups
open scoped ModularForm


private lemma sub_slash (k : ℤ) (B : Matrix.GeneralLinearGroup (Fin 2) ℝ) (f g : ℍ → ℂ) :
  SlashAction.map k B (f - g) = SlashAction.map k B f - SlashAction.map k B g := by
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]

private lemma slash_mapGL (k : ℤ) (f : ℍ → ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
  SlashAction.map k (Matrix.SpecialLinearGroup.mapGL ℝ γ) f = SlashAction.map k γ f := rfl

private lemma conj_det (p : ℕ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hc : (p : ℤ) ∣ γ 1 0) :
  Matrix.det (Matrix.of (Matrix.vecCons (Matrix.vecCons (γ 0 0) (Matrix.vecCons ((p : ℤ) * γ 0 1) Matrix.vecEmpty)) (Matrix.vecCons (Matrix.vecCons (γ 1 0 / (p : ℤ)) (Matrix.vecCons (γ 1 1) Matrix.vecEmpty)) Matrix.vecEmpty))) = 1 := by
  have h1 : (p : ℤ) * (γ 1 0 / (p : ℤ)) = γ 1 0 := Int.mul_ediv_cancel' hc
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h2 := γ.2
    rwa [Matrix.det_fin_two] at h2
  rw [Matrix.det_fin_two_of]
  have hb : (p : ℤ) * γ 0 1 * (γ 1 0 / (p : ℤ)) = γ 0 1 * γ 1 0 := by
    rw [mul_comm (p : ℤ) (γ 0 1), mul_assoc, h1]
  omega

private lemma val_heckeDiagMatrix_eq_map (p : ℕ) (hp : p ≠ 0) :
  ((ModularForm.heckeDiagMatrix p : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ((Matrix.of (Matrix.vecCons (Matrix.vecCons (p : ℤ) (Matrix.vecCons 0 Matrix.vecEmpty)) (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty)) Matrix.vecEmpty)))).map (algebraMap ℤ ℝ) := by
  rw [ModularForm.val_heckeDiagMatrix hp]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private lemma coe_mapGL_eq_map (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
  ((Matrix.SpecialLinearGroup.mapGL ℝ γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ((γ : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ ℝ) := rfl

private lemma heckeDiag_mul_mapGL (p : ℕ) (hp : p ≠ 0) (γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hZ : (Matrix.of (Matrix.vecCons (Matrix.vecCons (p : ℤ) (Matrix.vecCons 0 Matrix.vecEmpty)) (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty)) Matrix.vecEmpty))) * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * (Matrix.of (Matrix.vecCons (Matrix.vecCons (p : ℤ) (Matrix.vecCons 0 Matrix.vecEmpty)) (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty)) Matrix.vecEmpty)))) : ModularForm.heckeDiagMatrix p * Matrix.SpecialLinearGroup.mapGL ℝ γ = Matrix.SpecialLinearGroup.mapGL ℝ γ' * ModularForm.heckeDiagMatrix p := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_heckeDiagMatrix_eq_map p hp,
    coe_mapGL_eq_map, coe_mapGL_eq_map, ← Matrix.map_mul, ← Matrix.map_mul, hZ]

private lemma D2_slash_heckeDiag (p : ℕ) (hp : p ≠ 0) (γ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h10 : (γ' 1 0 : ℤ) = γ 1 0 / (p : ℤ)) (h11 : (γ' 1 1 : ℤ) = γ 1 1) (hc : (p : ℤ) ∣ γ 1 0) : SlashAction.map (2 : ℤ) (ModularForm.heckeDiagMatrix p) (EisensteinSeries.D2 γ') = EisensteinSeries.D2 γ := by
  ext τ
  rw [ModularForm.slash_heckeDiagMatrix_apply _ hp]
  simp only [EisensteinSeries.D2]
  rw [ModularGroup.denom_apply, ModularGroup.denom_apply, ModularForm.coe_heckeDiagMatrix_smul hp]
  have hdiv : ((γ 1 0 / (p : ℤ) : ℤ) : ℂ) * (p : ℂ) = ((γ 1 0 : ℤ) : ℂ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (Int.ediv_mul_cancel hc)
  have h10' : ((γ' 1 0 : ℤ) : ℂ) = ((γ 1 0 / (p : ℤ) : ℤ) : ℂ) := by exact_mod_cast h10
  have h11' : ((γ' 1 1 : ℤ) : ℂ) = ((γ 1 1 : ℤ) : ℂ) := by exact_mod_cast h11
  rw [h10', h11', show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one, ← mul_assoc, hdiv,
    mul_div_assoc']
  congr 1
  linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hdiv

private lemma ModularCurve.eisensteinTwoSlash_slash_eq_self (p : ℕ) [NeZero p] :
  ∀ γ ∈ ((CongruenceSubgroup.Gamma0 p : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
    SlashAction.map (2 : ℤ) γ (SlashAction.map (2 : ℤ) (ModularForm.heckeDiagMatrix p) EisensteinSeries.E2 - EisensteinSeries.E2) = SlashAction.map (2 : ℤ) (ModularForm.heckeDiagMatrix p) EisensteinSeries.E2 - EisensteinSeries.E2 := by
  have hp : p ≠ 0 := NeZero.ne p
  intro γ hγ
  obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.mp hγ
  have hc : (p : ℤ) ∣ γ₀ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (CongruenceSubgroup.Gamma0_mem.mp hγ₀)
  obtain ⟨γ', h10, h11, hval⟩ :
    ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (γ' 1 0 : ℤ) = γ₀ 1 0 / (p : ℤ) ∧ (γ' 1 1 : ℤ) = γ₀ 1 1 ∧
        (γ' : Matrix (Fin 2) (Fin 2) ℤ) = (Matrix.of (Matrix.vecCons (Matrix.vecCons (γ₀ 0 0) (Matrix.vecCons ((p : ℤ) * γ₀ 0 1) Matrix.vecEmpty)) (Matrix.vecCons (Matrix.vecCons (γ₀ 1 0 / (p : ℤ)) (Matrix.vecCons (γ₀ 1 1) Matrix.vecEmpty)) Matrix.vecEmpty))) :=
    ⟨⟨(Matrix.of (Matrix.vecCons (Matrix.vecCons (γ₀ 0 0) (Matrix.vecCons ((p : ℤ) * γ₀ 0 1) Matrix.vecEmpty)) (Matrix.vecCons (Matrix.vecCons (γ₀ 1 0 / (p : ℤ)) (Matrix.vecCons (γ₀ 1 1) Matrix.vecEmpty)) Matrix.vecEmpty))), conj_det p γ₀ hc⟩,
      rfl, rfl, rfl⟩
  have hZ : (Matrix.of (Matrix.vecCons (Matrix.vecCons (p : ℤ) (Matrix.vecCons 0 Matrix.vecEmpty)) (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty)) Matrix.vecEmpty))) * (γ₀ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * (Matrix.of (Matrix.vecCons (Matrix.vecCons (p : ℤ) (Matrix.vecCons 0 Matrix.vecEmpty)) (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty)) Matrix.vecEmpty))) := by
    rw [hval]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Int.ediv_mul_cancel hc, mul_comm]
  have hconj := heckeDiag_mul_mapGL p hp γ₀ γ' hZ
  rw [sub_slash, ← SlashAction.slash_mul, hconj, SlashAction.slash_mul,
    slash_mapGL, slash_mapGL,
    EisensteinSeries.E2_slash_action γ', EisensteinSeries.E2_slash_action γ₀,
    sub_slash, ModularForm.smul_slash, ModularForm.σ_heckeDiagMatrix,
    D2_slash_heckeDiag p hp γ₀ γ' h10 h11 hc]
  simp only [ContinuousAlgEquiv.refl_apply]
  abel

open scoped ModularForm in
/--
[ModularCurve_eisensteinTwoSlash_slash_eq_self](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_eisensteinTwoSlash_slash_eq_self.lean)
-/
@[path]
private lemma main :
-- imply
  ∀ (p : ℕ) [NeZero p], ∀ γ ∈ ((CongruenceSubgroup.Gamma0 p : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map (2 : ℤ) γ (SlashAction.map (2 : ℤ) (ModularForm.heckeDiagMatrix p) EisensteinSeries.E2 - EisensteinSeries.E2) = SlashAction.map (2 : ℤ) (ModularForm.heckeDiagMatrix p) EisensteinSeries.E2 - EisensteinSeries.E2 :=
-- proof
  @ModularCurve.eisensteinTwoSlash_slash_eq_self


-- created on 2026-10-23
