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
import Theorem.MeasureTheory.Geometry.BanachTarski.Part6


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- Mod-5 version of `btIntGen`, with the same coefficients. -/
def btIntGenMod (s : Fin 2 × Bool) (v : Fin 3 → ZMod 5) : Fin 3 → ZMod 5 :=
  if s = (0, true) then ![3 * v 0 - 4 * v 1, 4 * v 0 + 3 * v 1, 5 * v 2]
  else if s = (0, false) then ![3 * v 0 + 4 * v 1, -4 * v 0 + 3 * v 1, 5 * v 2]
  else if s = (1, true) then ![5 * v 0, 3 * v 1 - 4 * v 2, 4 * v 1 + 3 * v 2]
  else ![5 * v 0, 3 * v 1 + 4 * v 2, -4 * v 1 + 3 * v 2]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
