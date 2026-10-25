/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Theorem.v1.Atlas.GeometryOfManifolds.code.EuclideanDFS


noncomputable section

namespace EuclideanΩ

variable {n p : ℕ}

/-- Continuous-fibre version of `EuclideanΩ`: pointwise *continuous* alternating multilinear maps.
This is the regularity needed for the differential to be defined via `fderiv`. -/
abbrev CEuclideanΩ (n : ℕ) (p : ℕ) := Eℝ n → (Eℝ n [⋀^Fin p]→L[ℝ] ℝ)

end EuclideanΩ
end
