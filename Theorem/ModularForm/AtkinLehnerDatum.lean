module

public import Mathlib
public import Structure.ModularForm_AtkinLehnerDatum

public noncomputable section

set_option autoImplicit false

open Matrix UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularForm

variable (M q : ℕ)


namespace AtkinLehnerDatum

variable {M q : ℕ} (W : AtkinLehnerDatum M q)

public theorem hM_int : (M : ℤ) = (q : ℤ) * (W.R : ℤ) := by exact_mod_cast W.hM

include W in


public theorem q_pos [NeZero M] : 0 < q := by
  rcases Nat.eq_zero_or_pos q with h | h
  · exact absurd (W.hM.trans (Nat.mul_eq_zero.mpr (Or.inl h))) (NeZero.ne M)
  · exact h

include W in


public theorem R_pos [NeZero M] : 0 < W.R := by
  rcases Nat.eq_zero_or_pos W.R with h | h
  · exact absurd (W.hM.trans (Nat.mul_eq_zero.mpr (Or.inr h))) (NeZero.ne M)
  · exact h


@[simp] public theorem det_mat : W.mat.det = (q : ℤ) := by
  rw [mat, Matrix.det_fin_two_of]
  linear_combination (q : ℤ) * W.bezout


public theorem mat_lowerLeft : W.mat 1 0 = (M : ℤ) := by
  rw [mat, W.hM_int]
  simp


public theorem mat_sq : W.mat * W.mat = (q : ℤ) • W.sqUnit := by
  rw [mat, sqUnit, Matrix.mul_fin_two]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · show (q : ℤ) * W.a * ((q : ℤ) * W.a) + W.b * ((q : ℤ) * (W.R : ℤ))
      = (q : ℤ) * ((q : ℤ) * W.a ^ 2 + (W.R : ℤ) * W.b)
    ring
  · show (q : ℤ) * W.a * W.b + W.b * (q : ℤ) = (q : ℤ) * (W.b * (W.a + 1))
    ring
  · show (q : ℤ) * (W.R : ℤ) * ((q : ℤ) * W.a) + (q : ℤ) * ((q : ℤ) * (W.R : ℤ))
      = (q : ℤ) * ((q : ℤ) * (W.R : ℤ) * (W.a + 1))
    ring
  · show (q : ℤ) * (W.R : ℤ) * W.b + (q : ℤ) * (q : ℤ)
      = (q : ℤ) * ((W.R : ℤ) * W.b + (q : ℤ))
    ring


@[simp] public theorem det_sqUnit : W.sqUnit.det = 1 := by
  rw [sqUnit, Matrix.det_fin_two_of]
  linear_combination ((q : ℤ) * W.a - (W.R : ℤ) * W.b + 1) * W.bezout


@[simp] public theorem sqUnitSL_coe : (W.sqUnitSL : Matrix (Fin 2) (Fin 2) ℤ) = W.sqUnit := rfl


public theorem sqUnitSL_mem : W.sqUnitSL ∈ Gamma0 M := by
  rw [Gamma0_mem]
  show (((W.sqUnit 1 0 : ℤ) : ZMod M) = 0)
  have h : W.sqUnit 1 0 = (M : ℤ) * (W.a + 1) := by
    rw [sqUnit, W.hM_int]; simp
  rw [h]
  push_cast
  simp


@[simp] public theorem alGL_coe [NeZero M] :
    (W.alGL : Matrix (Fin 2) (Fin 2) ℝ) = (W.mat).map (algebraMap ℤ ℝ) := rfl


public theorem alGL_entry [NeZero M] (i j : Fin 2) :
    W.alGL i j = algebraMap ℤ ℝ (W.mat i j) := by
  show ((W.alGL : Matrix (Fin 2) (Fin 2) ℝ)) i j = _
  rw [alGL_coe, Matrix.map_apply]


public theorem val_det_alGL [NeZero M] : ((W.alGL).det : ℝ) = (q : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, alGL_coe]
  have h : ((W.mat).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) W.mat.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [h, W.det_mat]
  simp


public theorem det_alGL_pos [NeZero M] : 0 < ((W.alGL).det : ℝ) := by
  rw [val_det_alGL]
  exact_mod_cast W.q_pos


public theorem σ_alGL_apply [NeZero M] (z : ℂ) : σ W.alGL z = z := by
  rw [UpperHalfPlane.σ, ite_eq_left W.det_alGL_pos]
  simp


public theorem alGLQ_map_castHom [NeZero M] : (W.alGLQ).map (Rat.castHom ℝ) = W.alGL := by
  apply Units.ext
  show (Rat.castHom ℝ).mapMatrix ((W.alGLQ : Matrix (Fin 2) (Fin 2) ℚ))
      = (W.alGL : Matrix (Fin 2) (Fin 2) ℝ)
  show (Rat.castHom ℝ).mapMatrix ((W.mat).map (algebraMap ℤ ℚ))
      = (W.mat).map (algebraMap ℤ ℝ)
  rw [RingHom.mapMatrix_apply, Matrix.map_map]
  congr 1

end AtkinLehnerDatum


public theorem alSlash_def {M q : ℕ} (W : AtkinLehnerDatum M q) (k : ℤ) [NeZero M] (f : ℍ → ℂ) :
    alSlash W k f = f ∣[k] W.alGL := rfl


public theorem alSlash_add {M q : ℕ} (W : AtkinLehnerDatum M q) (k : ℤ) [NeZero M] (f g : ℍ → ℂ) :
    alSlash W k (f + g) = alSlash W k f + alSlash W k g := by
  simp only [alSlash, SlashAction.add_slash]


public theorem alSlash_smul {M q : ℕ} (W : AtkinLehnerDatum M q) (k : ℤ) [NeZero M] (c : ℂ) (f : ℍ → ℂ) :
    alSlash W k (c • f) = c • alSlash W k f := by
  simp only [alSlash, ModularForm.smul_slash, AtkinLehnerDatum.σ_alGL_apply]

end ModularForm

end
