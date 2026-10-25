/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Circle
import Structure.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part5
open Manifold

set_option autoImplicit false


noncomputable section

namespace GaugeActionData

attribute [instance] gaugeGroupGroup

/-- Equip the solution space with the canonical $\mathcal{G}$-action via `SMul`. -/
@[reducible] def toSMul
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc) :
    SMul gd.GaugeGroup (SWSolution spinc) :=
  ⟨gd.gauge_action⟩

end GaugeActionData


/-- The smooth gauge group $\mathcal{G} = \mathrm{Map}(M, S^1)$ of continuous (here, smooth)
circle-valued maps on $M$. -/
def SmoothGaugeGroup
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] :=
  { f : M → Circle // Continuous f }

/-- Evaluation of a smooth gauge transformation $f : M \to S^1$ at a point $x \in M$. -/
def SmoothGaugeGroup.eval
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (f : SmoothGaugeGroup M) (x : M) : Circle :=
  f.1 x

/-- The gauge-equivalence setoid on $\mathrm{SWSolution}$: two solutions are related iff one
is the image of the other under some $g \in \mathcal{G}$. -/
def GaugeActionData.gaugeEquivSetoid
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc) :
    Setoid (SWSolution spinc) where
  r sol₁ sol₂ := ∃ g : gd.GaugeGroup, gd.gauge_action g sol₁ = sol₂
  iseqv := {
    refl := fun sol => ⟨1, gd.gauge_action_one sol⟩
    symm := fun ⟨g, hg⟩ => ⟨g⁻¹, by
      rw [← hg, ← gd.gauge_action_mul, inv_mul_cancel, gd.gauge_action_one]⟩
    trans := fun ⟨g, hg⟩ ⟨h, hh⟩ => ⟨h * g, by
      rw [gd.gauge_action_mul, hg, hh]⟩
  }

/-- The Seiberg-Witten moduli quotient: the set-theoretic quotient
$\mathcal{M} = \{(A,\psi)\} / \mathcal{G}$ of solutions modulo gauge equivalence. -/
def SWModuliQuotient
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc) : Type _ :=
  Quotient gd.gaugeEquivSetoid

/-- The canonical projection $\mathrm{SWSolution} \to \mathrm{SWModuliQuotient}$ sending a
solution to its gauge equivalence class. -/
def SWModuliQuotient.mk
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gd : GaugeActionData spinc)
    (sol : SWSolution spinc) : SWModuliQuotient gd :=
  Quotient.mk gd.gaugeEquivSetoid sol


/-- A 2-form $\omega$ is self-dual if $*\omega = \omega$. -/
def IsSelfDual {Ω2 : Type*} (hodge_star : Ω2 → Ω2) (ω : Ω2) : Prop :=
  hodge_star ω = ω

/-- A 2-form $\omega$ is anti-self-dual if $*\omega = -\omega$. -/
def IsAntiSelfDual {Ω2 : Type*} [Neg Ω2] (hodge_star : Ω2 → Ω2) (ω : Ω2) : Prop :=
  hodge_star ω = -ω

end
