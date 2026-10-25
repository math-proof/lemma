/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Projection
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section30
open Matrix


section PoincareDuality

open CategoryTheory AlgebraicTopology LinearMap SingularCohomology

/-- Singular cohomology with coefficients in `F₂ = ZMod 2`, as a type. -/
abbrev SingularCohomology.CohomZMod2 (X : TopCat.{0}) (n : ℕ) : Type :=
  (singularCohomology (ZMod 2) X (ModuleCat.of (ZMod 2) (ZMod 2)) n : Type)

/-- Singular homology with coefficients in `F₂ = ZMod 2`, as a type. -/
abbrev HomolZMod2 (X : TopCat.{0}) (n : ℕ) : Type :=
  (singularHomologyModule (ZMod 2) X n : Type)

end PoincareDuality
