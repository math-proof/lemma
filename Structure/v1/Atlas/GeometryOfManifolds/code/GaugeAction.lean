/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/GaugeAction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.Topology.VectorBundle.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.GaugeAction
set_option autoImplicit false


noncomputable section

/-- Concrete data packaging the Seiberg–Witten setup on a $4$-manifold: spaces of connections, spinors, self-dual $2$-forms, the logarithmic derivative $f \mapsto f^{-1}df$, the Dirac operator, the self-dual curvature, Clifford multiplication, the traceless quadratic $\psi \otimes \psi^*$, and a perturbation $\mu$, together with the gauge-equivariance axioms. -/
structure ConcreteGaugeActionData
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2] where
  Connection : Type
  SpinorSection : Type
  NegativeSpinorSection : Type
  SelfDualTwoForm : Type
  [instACGConn : AddCommGroup Connection]
  [instModConn : Module ℝ Connection]
  [instACGSpinor : AddCommGroup SpinorSection]
  [instModSpinor : Module ℝ SpinorSection]
  [instACGNeg : AddCommGroup NegativeSpinorSection]
  [instModNeg : Module ℝ NegativeSpinorSection]
  [instACGSD : AddCommGroup SelfDualTwoForm]
  [instModSD : Module ℝ SelfDualTwoForm]
  instNontrivialSpinor : Nontrivial SpinorSection
  logDeriv : SWGaugeGroup M → Connection
  gaugeOnSpinor : SWGaugeGroup M → SpinorSection → SpinorSection
  supNormSq : SpinorSection → ℝ
  supNormSq_nonneg : ∀ (ψ : SpinorSection), 0 ≤ supNormSq ψ
  DiracOp : Connection → SpinorSection → NegativeSpinorSection
  selfDualCurvature : Connection → SelfDualTwoForm
  cliffordMap : SelfDualTwoForm → SpinorSection → SpinorSection
  tracelessQuadratic : SpinorSection → SpinorSection → SpinorSection
  perturbation : SelfDualTwoForm
  logDeriv_mul : ∀ (f g : SWGaugeGroup M), logDeriv (f * g) = logDeriv f + logDeriv g
  logDeriv_one : logDeriv 1 = 0
  logDeriv_const : ∀ (z : Circle), logDeriv (SWGaugeGroup.constEmb z) = 0
  gaugeOnSpinor_mul : ∀ (f g : SWGaugeGroup M) (ψ : SpinorSection),
    gaugeOnSpinor (f * g) ψ = gaugeOnSpinor f (gaugeOnSpinor g ψ)
  gaugeOnSpinor_one : ∀ (ψ : SpinorSection), gaugeOnSpinor 1 ψ = ψ
  gaugeOnSpinor_preserves_norm : ∀ (f : SWGaugeGroup M) (ψ : SpinorSection),
    supNormSq (gaugeOnSpinor f ψ) = supNormSq ψ
  gaugeOnNegSpinor : SWGaugeGroup M → NegativeSpinorSection → NegativeSpinorSection
  gaugeOnNegSpinor_zero : ∀ (f : SWGaugeGroup M), gaugeOnNegSpinor f 0 = 0
  DiracOp_gauge_equivariant : ∀ (f : SWGaugeGroup M) (A : Connection) (ψ : SpinorSection),
    DiracOp (A - (2 : ℝ) • logDeriv f) (gaugeOnSpinor f ψ) =
      gaugeOnNegSpinor f (DiracOp A ψ)
  selfDualCurvature_gauge_invariant : ∀ (f : SWGaugeGroup M) (A : Connection),
    selfDualCurvature (A - (2 : ℝ) • logDeriv f) = selfDualCurvature A
  tracelessQuadratic_gauge_invariant : ∀ (f : SWGaugeGroup M) (ψ φ : SpinorSection),
    tracelessQuadratic (gaugeOnSpinor f ψ) φ = tracelessQuadratic ψ φ

end
