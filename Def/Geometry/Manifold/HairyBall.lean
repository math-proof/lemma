/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/HairyBall.lean -/

/- Authors: Adam Kiezun, Muse Spark 1.3 -/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Normed.Module.Ray

@[expose] public section

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
