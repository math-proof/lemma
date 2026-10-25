/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean -/

/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.LinearAlgebra.Orientation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Data.Set.Card
import Mathlib.Analysis.Convex.Independent
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Def.Geometry.Metric.Part2
import Lemma.Set.Metric
import Lemma.Set.Triplewise
import Mathlib.Logic.Equiv.Fin.Rotate
import Def.Data.Set.Triplewise
open scoped EuclideanGeometry Finset


/-- Oriented angles make sense in 2d.

Note: this can't blindly be added to mathlib as it creates an "instance diamond"
with an instance for modules satisfying `is_empty`. -/
noncomputable instance Module.orientedEuclideanSpaceFinTwo : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨Basis.orientation <| PiLp.basisFun 2 _ _⟩

