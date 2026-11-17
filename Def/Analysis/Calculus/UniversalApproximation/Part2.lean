module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Theorem.Analysis.Calculus.UniversalApproximation

@[expose] public section

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
