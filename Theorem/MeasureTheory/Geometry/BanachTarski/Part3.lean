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
import Def.MeasureTheory.Geometry.BanachTarski.Part3


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
