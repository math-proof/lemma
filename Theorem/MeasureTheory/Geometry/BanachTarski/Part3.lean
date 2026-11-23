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
public import Def.MeasureTheory.Geometry.BanachTarski.Part3

public section

namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- Iterates of the rotation isometries. -/
theorem btRotY_iterate (t : ℝ) (n : ℕ) (x : btE) :
    (btIsoOfUnitary (btRotY t))^[n] x = btIsoOfUnitary (btRotY (n * t)) x := by
  induction n with
  | zero => simp [Function.iterate_zero_apply, btRotY_zero, btIsoOfUnitary_one]
  | succ n ih =>
    rw [show n + 1 = n.succ from rfl, Function.iterate_succ_apply', ih,
      ← btIsoOfUnitary_mul, ← btRotY_add]
    have hcast : ((n + 1 : ℕ) : ℝ) * t = t + (n : ℝ) * t := by push_cast; ring
    rw [hcast]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
