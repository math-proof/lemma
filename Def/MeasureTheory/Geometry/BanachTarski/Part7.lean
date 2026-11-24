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
public import Theorem.MeasureTheory.Geometry.BanachTarski.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- Mod-5 version of `btIntGen`, with the same coefficients. -/
def btIntGenMod (s : Fin 2 × Bool) (v : Fin 3 → ZMod 5) : Fin 3 → ZMod 5 :=
  if s = (0, true) then ![3 * v 0 - 4 * v 1, 4 * v 0 + 3 * v 1, 5 * v 2]
  else if s = (0, false) then ![3 * v 0 + 4 * v 1, -4 * v 0 + 3 * v 1, 5 * v 2]
  else if s = (1, true) then ![5 * v 0, 3 * v 1 - 4 * v 2, 4 * v 1 + 3 * v 2]
  else ![5 * v 0, 3 * v 1 + 4 * v 2, -4 * v 1 + 3 * v 2]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
