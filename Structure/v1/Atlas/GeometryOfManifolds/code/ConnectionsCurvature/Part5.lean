/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ConnectionsCurvature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Def.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part6
open Bundle NormedSpace
open scoped Manifold ContDiff Topology

open DifferentialFormSpace


/-- Data for the Chern connection in a holomorphic frame: a connection form $A$ with the
decomposition $d = \partial + \bar\partial$ and the identity $\partial A = -A \wedge A$. -/
structure HolomorphicFrameData (R : Type*) [Ring R] where
  A : R
  d : R → R
  del : R → R
  dbar : R → R
  d_eq_del_add_dbar : ∀ x, d x = del x + dbar x
  del_A_eq : del A = -(A * A)

