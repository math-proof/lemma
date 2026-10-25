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
import Structure.v1.Atlas.GeometryOfManifolds.code.GaugeAction
set_option autoImplicit false


noncomputable section

namespace ConcreteGaugeActionData

attribute [instance] instACGConn instModConn instACGSpinor instModSpinor instACGNeg instModNeg
  instACGSD instModSD instNontrivialSpinor

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

variable {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]

variable (ga : @ConcreteGaugeActionData M _ _ Ω1 Ω2 _ _ _ _)

/-- The gauge action on a connection: $A \mapsto A - 2 f^{-1} df$. -/
def gaugeOnConnection (f : SWGaugeGroup M) (A : ga.Connection) : ga.Connection :=
  A - (2 : ℝ) • ga.logDeriv f

/-- The combined gauge action on pairs $(A, \psi) \mapsto (A - 2 df \cdot f^{-1}, f\psi)$. -/
def gaugeAction (f : SWGaugeGroup M) (p : ga.Connection × ga.SpinorSection) :
    ga.Connection × ga.SpinorSection :=
  (ga.gaugeOnConnection f p.1, ga.gaugeOnSpinor f p.2)

/-- The (perturbed) Seiberg–Witten equations: $D_A \psi = 0$ and $F_A^+ \cdot \varphi = \sigma(\psi)\varphi - \mu \cdot \varphi$ for all spinors $\varphi$. -/
def IsSWSolution (A : ga.Connection) (ψ : ga.SpinorSection) : Prop :=
  ga.DiracOp A ψ = 0 ∧
  (∀ φ : ga.SpinorSection,
    ga.cliffordMap (ga.selfDualCurvature A) φ =
      ga.tracelessQuadratic ψ φ - ga.cliffordMap ga.perturbation φ)

end ConcreteGaugeActionData
end
