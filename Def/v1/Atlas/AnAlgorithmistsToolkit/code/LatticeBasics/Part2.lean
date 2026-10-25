/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LatticeBasics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Group.Int.Units
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Inductive.v1.Atlas.AnAlgorithmistsToolkit.code.LatticeBasics
open Matrix BigOperators


namespace LatticeBasics

open Submodule Set

noncomputable def latticeDet (n m : ℕ) (b : Fin n → (Fin m → ℝ)) : ℝ :=
  Real.sqrt ((Matrix.of b) * (Matrix.of b)ᵀ).det

noncomputable def successiveMinimum (m : ℕ) (L : Submodule ℤ (Fin m → ℝ)) (i : ℕ) : ℝ :=
  sInf {r : ℝ | i ≤ Module.finrank ℝ
    (Submodule.span ℝ ((↑L : Set (Fin m → ℝ)) ∩ Metric.closedBall 0 r))}

end LatticeBasics
