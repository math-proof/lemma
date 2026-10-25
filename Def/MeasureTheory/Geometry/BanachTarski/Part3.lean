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
import Theorem.MeasureTheory.Geometry.BanachTarski.Part2


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
