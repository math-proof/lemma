/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.MetricSpace.IsometricSMul
import Def.MeasureTheory.Geometry.BanachTarski.Part6


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- The first generator preserves cross products. -/
theorem btCross_genA (u v : Fin 3 → ℝ) :
    crossProduct
        (Matrix.mulVec (btGenA : Matrix (Fin 3) (Fin 3) ℝ) u)
        (Matrix.mulVec (btGenA : Matrix (Fin 3) (Fin 3) ℝ) v) =
      Matrix.mulVec (btGenA : Matrix (Fin 3) (Fin 3) ℝ)
        (crossProduct u v) := by
  rw [btGenA_mat]
  ext i
  fin_cases i <;>
    simp only [cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_succ',
      Matrix.head_cons, Matrix.head_fin_const] <;>
    ring

/-- The second generator preserves cross products. -/
theorem btCross_genB (u v : Fin 3 → ℝ) :
    crossProduct
        (Matrix.mulVec (btGenB : Matrix (Fin 3) (Fin 3) ℝ) u)
        (Matrix.mulVec (btGenB : Matrix (Fin 3) (Fin 3) ℝ) v) =
      Matrix.mulVec (btGenB : Matrix (Fin 3) (Fin 3) ℝ)
        (crossProduct u v) := by
  rw [btGenB_mat]
  ext i
  fin_cases i <;>
    simp only [cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_succ',
      Matrix.head_cons, Matrix.head_fin_const] <;>
    ring

/-- The transpose of a cross-preserving orthogonal matrix preserves cross
products. -/
theorem btCross_transpose (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M ∈ Matrix.unitaryGroup (Fin 3) ℝ)
    (hcross : ∀ u v : Fin 3 → ℝ,
      crossProduct (Matrix.mulVec M u) (Matrix.mulVec M v) =
        Matrix.mulVec M (crossProduct u v)) (u v : Fin 3 → ℝ) :
    crossProduct
        (Matrix.mulVec (Matrix.transpose M) u)
        (Matrix.mulVec (Matrix.transpose M) v) =
      Matrix.mulVec (Matrix.transpose M) (crossProduct u v) := by
  have hMtM : Matrix.transpose M * M = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hM
    rwa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hMMt : M * Matrix.transpose M = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hM
    rwa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hinj : Function.Injective (Matrix.mulVec M) := by
    intro a b hab
    have h2 := congrArg (Matrix.mulVec (Matrix.transpose M)) hab
    simp only [Matrix.mulVec_mulVec, hMtM, Matrix.one_mulVec] at h2
    exact h2
  have e : ∀ w : Fin 3 → ℝ,
      Matrix.mulVec M (Matrix.mulVec (Matrix.transpose M) w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, hMMt, Matrix.one_mulVec]
  apply hinj
  simp only [← hcross, e]

/-- Every matrix in the image preserves cross products. -/
theorem btRho_cross (w : FreeGroup (Fin 2)) (u v : Fin 3 → ℝ) :
    crossProduct
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) u)
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) v) =
      Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) (crossProduct u v) := by
  induction w using FreeGroup.induction_on generalizing u v with
  | one =>
    simp only [map_one, Submonoid.coe_one, Matrix.one_mulVec]
  | of x =>
    have hx : x = 0 ∨ x = 1 := by fin_cases x <;> simp
    rcases hx with rfl | rfl
    · have h0 : (btRho (FreeGroup.of (0 : Fin 2)) : Matrix (Fin 3) (Fin 3) ℝ)
          = (btGenA : Matrix (Fin 3) (Fin 3) ℝ) := by
        simp only [btRho, FreeGroup.lift_apply_of, btGenFun,
          Matrix.cons_val_zero]
      rw [h0]
      exact btCross_genA u v
    · have h1 : (btRho (FreeGroup.of (1 : Fin 2)) : Matrix (Fin 3) (Fin 3) ℝ)
          = (btGenB : Matrix (Fin 3) (Fin 3) ℝ) := by
        simp only [btRho, FreeGroup.lift_apply_of, btGenFun,
          Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [h1]
      exact btCross_genB u v
  | inv_of x ih =>
    have hM : (btRho ((FreeGroup.of x)⁻¹) : Matrix (Fin 3) (Fin 3) ℝ)
        = Matrix.transpose (btRho (FreeGroup.of x) : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star,
        Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [hM]
    exact btCross_transpose _ (btRho (FreeGroup.of x)).2 ih u v
  | mul x y ihx ihy =>
    have hM : (btRho (x * y) : Matrix (Fin 3) (Fin 3) ℝ)
        = (btRho x : Matrix (Fin 3) (Fin 3) ℝ)
          * (btRho y : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [map_mul, Submonoid.coe_mul]
    rw [hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ihx, ihy,
      Matrix.mulVec_mulVec]

/-- Every matrix in the image is orthogonal. -/
theorem btRho_star_mul (w : FreeGroup (Fin 2)) :
    star (btRho w : Matrix (Fin 3) (Fin 3) ℝ) * (btRho w : Matrix (Fin 3) (Fin 3) ℝ) = 1 :=
  (Matrix.mem_unitaryGroup_iff').mp (btRho w).2

/-- Every matrix in the image preserves dot products. -/
theorem btRho_dot (w : FreeGroup (Fin 2)) (u v : Fin 3 → ℝ) :
    dotProduct
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) u)
        (Matrix.mulVec (btRho w : Matrix (Fin 3) (Fin 3) ℝ) v) =
      dotProduct u v := by
  have hort : Matrix.transpose (btRho w : Matrix (Fin 3) (Fin 3) ℝ)
      * (btRho w : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    have h := btRho_star_mul w
    rwa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hort, Matrix.vecMul_one]

/-- Transposes of the generators in explicit form. -/
theorem btGenA_transpose :
    Matrix.transpose (btGenA : Matrix (Fin 3) (Fin 3) ℝ) =
      !![(3 : ℝ) / 5, 4 / 5, 0; -(4 / 5), 3 / 5, 0; 0, 0, 1] := by
  rw [btGenA_mat]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem btGenB_transpose :
    Matrix.transpose (btGenB : Matrix (Fin 3) (Fin 3) ℝ) =
      !![(1 : ℝ), 0, 0; 0, 3 / 5, 4 / 5; 0, -(4 / 5), 3 / 5] := by
  rw [btGenB_mat]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Five times a generator acts integrally on integer vectors. -/
theorem btFiveGenA (v : Fin 3 → ℤ) :
    Matrix.mulVec ((5 : ℝ) • (btGenA : Matrix (Fin 3) (Fin 3) ℝ))
        (fun i => ((v i : ℤ) : ℝ)) =
      fun i => (((btIntGen (0, true) v) i : ℤ) : ℝ) := by
  rw [btGenA_mat]
  ext i
  fin_cases i <;>
    simp [smul_eq_mul, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, btIntGen] <;>
    ring

theorem btFiveGenAinv (v : Fin 3 → ℤ) :
    Matrix.mulVec ((5 : ℝ) • Matrix.transpose (btGenA : Matrix (Fin 3) (Fin 3) ℝ))
        (fun i => ((v i : ℤ) : ℝ)) =
      fun i => (((btIntGen (0, false) v) i : ℤ) : ℝ) := by
  rw [btGenA_transpose]
  ext i
  fin_cases i <;>
    simp [smul_eq_mul, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, btIntGen] <;>
    ring

theorem btFiveGenB (v : Fin 3 → ℤ) :
    Matrix.mulVec ((5 : ℝ) • (btGenB : Matrix (Fin 3) (Fin 3) ℝ))
        (fun i => ((v i : ℤ) : ℝ)) =
      fun i => (((btIntGen (1, true) v) i : ℤ) : ℝ) := by
  rw [btGenB_mat]
  ext i
  fin_cases i <;>
    simp [smul_eq_mul, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, btIntGen] <;>
    ring

theorem btFiveGenBinv (v : Fin 3 → ℤ) :
    Matrix.mulVec ((5 : ℝ) • Matrix.transpose (btGenB : Matrix (Fin 3) (Fin 3) ℝ))
        (fun i => ((v i : ℤ) : ℝ)) =
      fun i => (((btIntGen (1, false) v) i : ℤ) : ℝ) := by
  rw [btGenB_transpose]
  ext i
  fin_cases i <;>
    simp [smul_eq_mul, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, btIntGen] <;>
    ring

/-- Single-letter step of the integer model. -/
theorem btFiveGen_single (s : Fin 2 × Bool) (v : Fin 3 → ℤ) :
    Matrix.mulVec ((5 : ℝ) • (btRho (FreeGroup.mk [s]) : Matrix (Fin 3) (Fin 3) ℝ))
        (fun i => ((v i : ℤ) : ℝ)) =
      fun i => (((btIntGen s v) i : ℤ) : ℝ) := by
  obtain ⟨x, b⟩ := s
  have hx : x = 0 ∨ x = 1 := by fin_cases x <;> simp
  rcases hx with rfl | rfl <;> cases b
  · have h1 : FreeGroup.mk [((0 : Fin 2), false)] = (FreeGroup.of (0 : Fin 2))⁻¹ := by
      have ho : FreeGroup.of (0 : Fin 2) = FreeGroup.mk [((0 : Fin 2), true)] := rfl
      rw [ho, FreeGroup.inv_mk]
      rfl
    have h0 : btRho (FreeGroup.of (0 : Fin 2)) = btGenA := by
      simp only [btRho, FreeGroup.lift_apply_of, btGenFun, Matrix.cons_val_zero]
    have hA : (btRho (FreeGroup.mk [((0 : Fin 2), false)]) : Matrix (Fin 3) (Fin 3) ℝ)
        = Matrix.transpose (btGenA : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [h1, map_inv, ← Unitary.star_eq_inv, Unitary.coe_star,
        Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, h0]
    rw [hA]
    exact btFiveGenAinv v
  · have h1 : FreeGroup.mk [((0 : Fin 2), true)] = FreeGroup.of (0 : Fin 2) := rfl
    have h0 : btRho (FreeGroup.of (0 : Fin 2)) = btGenA := by
      simp only [btRho, FreeGroup.lift_apply_of, btGenFun, Matrix.cons_val_zero]
    have hA : (btRho (FreeGroup.mk [((0 : Fin 2), true)]) : Matrix (Fin 3) (Fin 3) ℝ)
        = (btGenA : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [h1, h0]
    rw [hA]
    exact btFiveGenA v
  · have h1 : FreeGroup.mk [((1 : Fin 2), false)] = (FreeGroup.of (1 : Fin 2))⁻¹ := by
      have ho : FreeGroup.of (1 : Fin 2) = FreeGroup.mk [((1 : Fin 2), true)] := rfl
      rw [ho, FreeGroup.inv_mk]
      rfl
    have h0 : btRho (FreeGroup.of (1 : Fin 2)) = btGenB := by
      simp only [btRho, FreeGroup.lift_apply_of, btGenFun, Matrix.cons_val_one,
        Matrix.cons_val_zero]
    have hA : (btRho (FreeGroup.mk [((1 : Fin 2), false)]) : Matrix (Fin 3) (Fin 3) ℝ)
        = Matrix.transpose (btGenB : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [h1, map_inv, ← Unitary.star_eq_inv, Unitary.coe_star,
        Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, h0]
    rw [hA]
    exact btFiveGenBinv v
  · have h1 : FreeGroup.mk [((1 : Fin 2), true)] = FreeGroup.of (1 : Fin 2) := rfl
    have h0 : btRho (FreeGroup.of (1 : Fin 2)) = btGenB := by
      simp only [btRho, FreeGroup.lift_apply_of, btGenFun, Matrix.cons_val_one,
        Matrix.cons_val_zero]
    have hA : (btRho (FreeGroup.mk [((1 : Fin 2), true)]) : Matrix (Fin 3) (Fin 3) ℝ)
        = (btGenB : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [h1, h0]
    rw [hA]
    exact btFiveGenB v

/-- The integer model computes `5 ^ |L| • M_L e_y`. -/
theorem btIntWord_spec (L : List (Fin 2 × Bool)) :
    (5 ^ L.length : ℝ) •
        (Matrix.mulVec (btRho (FreeGroup.mk L) : Matrix (Fin 3) (Fin 3) ℝ) ![0, 1, 0]) =
    fun i => ((btIntWord L i : ℤ) : ℝ) := by
  induction L with
  | nil =>
    have h1 : btRho (FreeGroup.mk []) = 1 := by
      simp only [btRho, FreeGroup.lift_mk, List.map_nil, List.prod_nil]
    simp only [List.length_nil, pow_zero, one_smul, h1, Submonoid.coe_one,
      Matrix.one_mulVec, btIntWord, List.foldr_nil]
    ext i
    fin_cases i <;> simp
  | cons s L' ih =>
    have hmk : FreeGroup.mk [s] * FreeGroup.mk L' = FreeGroup.mk (s :: L') :=
      FreeGroup.mul_mk
    have hM : (btRho (FreeGroup.mk (s :: L')) : Matrix (Fin 3) (Fin 3) ℝ)
        = (btRho (FreeGroup.mk [s]) : Matrix (Fin 3) (Fin 3) ℝ)
          * (btRho (FreeGroup.mk L') : Matrix (Fin 3) (Fin 3) ℝ) := by
      rw [← hmk, map_mul, Submonoid.coe_mul]
    have hscale : (5 : ℝ) ^ (L'.length + 1)
          • (Matrix.mulVec (((btRho (FreeGroup.mk [s]) : Matrix (Fin 3) (Fin 3) ℝ)
            * (btRho (FreeGroup.mk L') : Matrix (Fin 3) (Fin 3) ℝ)))
            ![0, 1, (0 : ℝ)]) =
        Matrix.mulVec ((5 : ℝ) • (btRho (FreeGroup.mk [s]) : Matrix (Fin 3) (Fin 3) ℝ))
          ((5 : ℝ) ^ L'.length
            • Matrix.mulVec (btRho (FreeGroup.mk L') : Matrix (Fin 3) (Fin 3) ℝ)
              ![0, 1, (0 : ℝ)]) := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, ← mul_smul, ← pow_succ',
        Matrix.mulVec_mulVec]
    rw [hM, List.length_cons, hscale, ih, btFiveGen_single]
    simp only [btIntWord, List.foldr_cons]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
