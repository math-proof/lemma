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
public import Theorem.MeasureTheory.Geometry.BanachTarski.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- Five times the generator for a letter, on integer vectors. -/
def btIntGen (s : Fin 2 × Bool) (v : Fin 3 → ℤ) : Fin 3 → ℤ :=
  if s = (0, true) then ![3 * v 0 - 4 * v 1, 4 * v 0 + 3 * v 1, 5 * v 2]
  else if s = (0, false) then ![3 * v 0 + 4 * v 1, -4 * v 0 + 3 * v 1, 5 * v 2]
  else if s = (1, true) then ![5 * v 0, 3 * v 1 - 4 * v 2, 4 * v 1 + 3 * v 2]
  else ![5 * v 0, 3 * v 1 + 4 * v 2, -4 * v 1 + 3 * v 2]

/-- Right fold of `btIntGen` over a word, starting from `e_y = (0, 1, 0)`. -/
def btIntWord (L : List (Fin 2 × Bool)) : Fin 3 → ℤ :=
  L.foldr btIntGen ![0, 1, 0]

/-- The mod-5 direction of the first letter. -/
def btEll (s : Fin 2 × Bool) : Fin 3 → ZMod 5 :=
  if s = (0, true) then ![1, 3, 0]
  else if s = (0, false) then ![3, 1, 0]
  else if s = (1, true) then ![0, 1, 3]
  else ![0, 3, 1]

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
