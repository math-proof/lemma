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
public import Theorem.MeasureTheory.Geometry.BanachTarski.Part2

@[expose] public section

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- Rotation about the z-axis. -/
noncomputable def btRotZ (θ : ℝ) : Matrix.unitaryGroup (Fin 3) ℝ :=
  ⟨!![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, (1 : ℝ)],
    btRotBlock_mem (Real.cos θ) (Real.sin θ)
      (by linear_combination Real.cos_sq_add_sin_sq θ)⟩

/-- Rotation about the y-axis. -/
noncomputable def btRotY (θ : ℝ) : Matrix.unitaryGroup (Fin 3) ℝ :=
  ⟨!![Real.cos θ, 0, -Real.sin θ; 0, 1, 0; Real.sin θ, 0, (Real.cos θ : ℝ)],
    btRotBlockY_mem (Real.cos θ) (Real.sin θ)
      (by linear_combination Real.cos_sq_add_sin_sq θ)⟩

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
