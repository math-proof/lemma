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
import Theorem.MeasureTheory.Geometry.BanachTarski.Part14


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- Second centre at distance 3 on the x-axis. -/
def btC₂ : btE := WithLp.toLp 2 ![3, 0, (0 : ℝ)]

/-- Translation by the second centre. -/
noncomputable def btShift : btE ≃ᵢ btE := IsometryEquiv.addRight btC₂

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
