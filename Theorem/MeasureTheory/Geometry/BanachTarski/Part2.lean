/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.SetTheory.Cardinal.Free
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Real.Pi.Irrational
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Def.MeasureTheory.Geometry.BanachTarski.Part2

public section

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- Applying the isometry is matrix-times-vector on coordinates. -/
theorem btIsoOfUnitary_apply (U : Matrix.unitaryGroup (Fin 3) ℝ) (x : btE) :
    WithLp.ofLp (btIsoOfUnitary U x) =
      Matrix.mulVec (U : Matrix (Fin 3) (Fin 3) ℝ) (WithLp.ofLp x) := rfl

/-- The action is multiplicative. -/
theorem btIsoOfUnitary_mul (U V : Matrix.unitaryGroup (Fin 3) ℝ) (x : btE) :
    btIsoOfUnitary (U * V) x = btIsoOfUnitary U (btIsoOfUnitary V x) := by
  apply WithLp.ofLp_injective
  simp only [btIsoOfUnitary_apply, Submonoid.coe_mul, Matrix.mulVec_mulVec]

/-- The action of the identity matrix is the identity. -/
theorem btIsoOfUnitary_one (x : btE) :
    btIsoOfUnitary 1 x = x := by
  apply WithLp.ofLp_injective
  simp only [btIsoOfUnitary_apply, Submonoid.coe_one, Matrix.one_mulVec]

/-- A 2D rotation block in the (0, 1)-plane is unitary when `c ^ 2 + s ^ 2 = 1`. -/
theorem btRotBlock_mem (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    !![c, -s, 0; s, c, 0; 0, 0, (1 : ℝ)] ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
  have hT : Matrix.transpose !![c, -s, 0; s, c, 0; 0, 0, (1 : ℝ)]
      = !![c, s, 0; -s, c, 0; 0, 0, (1 : ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have e00 : c * c + -s * -s + 0 * 0 = (1 : ℝ) := by linear_combination h
  have e01 : c * s + -s * c + 0 * 0 = (0 : ℝ) := by ring
  have e02 : c * 0 + -s * 0 + 0 * 1 = (0 : ℝ) := by ring
  have e10 : s * c + c * -s + 0 * 0 = (0 : ℝ) := by ring
  have e11 : s * s + c * c + 0 * 0 = (1 : ℝ) := by linear_combination h
  have e12 : s * 0 + c * 0 + 0 * 1 = (0 : ℝ) := by ring
  have e20 : 0 * c + 0 * -s + 1 * 0 = (0 : ℝ) := by ring
  have e21 : 0 * s + 0 * c + 1 * 0 = (0 : ℝ) := by ring
  have e22 : 0 * 0 + 0 * 0 + 1 * 1 = (1 : ℝ) := by ring
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, hT, Matrix.mul_fin_three,
    Matrix.one_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

/-- A 2D rotation block in the (0, 2)-plane is unitary when `c ^ 2 + s ^ 2 = 1`. -/
theorem btRotBlockY_mem (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    !![c, 0, -s; 0, 1, 0; s, 0, (c : ℝ)] ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
  have hT : Matrix.transpose !![c, 0, -s; 0, 1, 0; s, 0, (c : ℝ)]
      = !![c, 0, s; 0, 1, 0; -s, 0, (c : ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have e00 : c * c + 0 * 0 + -s * -s = (1 : ℝ) := by linear_combination h
  have e01 : c * 0 + 0 * 1 + -s * 0 = (0 : ℝ) := by ring
  have e02 : c * s + 0 * 0 + -s * c = (0 : ℝ) := by ring
  have e10 : 0 * c + 1 * 0 + 0 * -s = (0 : ℝ) := by ring
  have e11 : 0 * 0 + 1 * 1 + 0 * 0 = (1 : ℝ) := by ring
  have e12 : 0 * s + 1 * 0 + 0 * c = (0 : ℝ) := by ring
  have e20 : s * c + 0 * 0 + c * -s = (0 : ℝ) := by ring
  have e21 : s * 0 + 0 * 1 + c * 0 = (0 : ℝ) := by ring
  have e22 : s * s + 0 * 0 + c * c = (1 : ℝ) := by linear_combination h
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, hT, Matrix.mul_fin_three,
    Matrix.one_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

/-- A 2D rotation block in the (1, 2)-plane is unitary when `c ^ 2 + s ^ 2 = 1`. -/
theorem btRotBlockX_mem (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    !![(1 : ℝ), 0, 0; 0, c, -s; 0, s, c] ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
  have hT : Matrix.transpose !![(1 : ℝ), 0, 0; 0, c, -s; 0, s, c]
      = !![(1 : ℝ), 0, 0; 0, c, s; 0, -s, c] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have e00 : 1 * 1 + 0 * 0 + 0 * 0 = (1 : ℝ) := by ring
  have e01 : 1 * 0 + 0 * c + 0 * -s = (0 : ℝ) := by ring
  have e02 : 1 * 0 + 0 * s + 0 * c = (0 : ℝ) := by ring
  have e10 : 0 * 1 + c * 0 + -s * 0 = (0 : ℝ) := by ring
  have e11 : 0 * 0 + c * c + -s * -s = (1 : ℝ) := by linear_combination h
  have e12 : 0 * 0 + c * s + -s * c = (0 : ℝ) := by ring
  have e20 : 0 * 1 + s * 0 + c * 0 = (0 : ℝ) := by ring
  have e21 : 0 * 0 + s * c + c * -s = (0 : ℝ) := by ring
  have e22 : 0 * 0 + s * s + c * c = (1 : ℝ) := by linear_combination h
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, hT, Matrix.mul_fin_three,
    Matrix.one_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
