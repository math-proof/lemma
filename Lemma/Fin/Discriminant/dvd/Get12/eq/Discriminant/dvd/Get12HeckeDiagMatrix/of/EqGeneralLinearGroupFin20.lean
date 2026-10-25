import Mathlib
import sympy.Basic
import Lemma.ModularForm.HeckeOperator
open UpperHalfPlane Matrix MatrixGroups
open scoped ModularForm


private lemma slash_mapGL (k : ℤ) (f : ℍ → ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
  SlashAction.map k (Matrix.SpecialLinearGroup.mapGL ℝ γ) f = SlashAction.map k γ f := rfl

private lemma coe_mapGL_eq_map (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
  ((Matrix.SpecialLinearGroup.mapGL ℝ γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ)
    = ((γ : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ ℝ) := rfl

private lemma ModularCurve.discriminant_slash_fricke_eq_discriminant_slash_heckeDiagMatrix (p : ℕ) [NeZero p] (W : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hW : ((W : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.of (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons (-1) Matrix.vecEmpty)) (Matrix.vecCons (Matrix.vecCons (p : ℝ) (Matrix.vecCons 0 Matrix.vecEmpty)) Matrix.vecEmpty))) : SlashAction.map (12 : ℤ) W ModularForm.discriminant = SlashAction.map (12 : ℤ) (ModularForm.heckeDiagMatrix p) ModularForm.discriminant := by
  have hp : p ≠ 0 := NeZero.ne p
  have hS : ((Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S :
    Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.of (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons (-1) Matrix.vecEmpty)) (Matrix.vecCons (Matrix.vecCons 1 (Matrix.vecCons 0 Matrix.vecEmpty)) Matrix.vecEmpty)) := by
    rw [coe_mapGL_eq_map, ModularGroup.coe_S]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hW1 : W = Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S * ModularForm.heckeDiagMatrix p := by
    apply Units.ext
    rw [Units.val_mul, hS, ModularForm.val_heckeDiagMatrix hp, hW]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hW1, SlashAction.slash_mul, slash_mapGL, ModularForm.discriminant_S_invariant]
/--
[ModularCurve_discriminant_slash_fricke_eq_discriminant_slash_heckeDiagMatrix](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_discriminant_slash_fricke_eq_discriminant_slash_heckeDiagMatrix.lean)
-/
@[path]
private lemma main
  {p : ℕ} [NeZero p]
  {W : Matrix.GeneralLinearGroup (Fin 2) ℝ}
-- given
  (hW : ((W : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.of (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons (-1) Matrix.vecEmpty)) (Matrix.vecCons (Matrix.vecCons (p : ℝ) (Matrix.vecCons 0 Matrix.vecEmpty)) Matrix.vecEmpty))) :
-- imply
  SlashAction.map (12 : ℤ) W ModularForm.discriminant = SlashAction.map (12 : ℤ) (ModularForm.heckeDiagMatrix p) ModularForm.discriminant :=
-- proof
  ModularCurve.discriminant_slash_fricke_eq_discriminant_slash_heckeDiagMatrix p W hW


-- created on 2026-10-23
