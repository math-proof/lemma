/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/HairyBall.lean -/

/- Authors: Adam Kiezun, Muse Spark 1.3 -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Module.Ray


namespace MathlibExt.Geometry.Manifold.HairyBallWanted

open Metric

open scoped Pointwise

/-- Step 2: homogeneous unit tangent field `V` from smooth `h`.
`V 0 = 0`, `V x = (‖x‖ / ‖h(νx)‖) • h(νx)` for `x ≠ 0`. -/
noncomputable def VHair
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : E → E) (x : E) : E :=
  letI := Classical.propDecidable (x = 0)
  if x = 0 then 0 else (‖x‖ / ‖h (‖x‖⁻¹ • x)‖) • h (‖x‖⁻¹ • x)

end MathlibExt.Geometry.Manifold.HairyBallWanted
