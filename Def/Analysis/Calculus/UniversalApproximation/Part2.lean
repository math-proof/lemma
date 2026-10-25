import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.UniformSpace.HeineCantor
import Theorem.Analysis.Calculus.UniversalApproximation
open scoped BigOperators Pointwise

/-!
# Universal approximation theorem

Proves `Wanted` entry `universal_approximation`.
-/


namespace MetaMathlibExt.UniversalApprox

noncomputable def mollify (φ : ContDiffBump (0 : ℝ)) (σ : ℝ → ℝ) :
    ℝ → ℝ :=
  MeasureTheory.convolution (φ.normed MeasureTheory.volume) σ
    (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume

end MetaMathlibExt.UniversalApprox
