/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LatticeBasics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Inductive.v1.Atlas.AnAlgorithmistsToolkit.code.LatticeBasics

@[expose] public section

open Matrix BigOperators


namespace LatticeBasics

open Submodule Set

noncomputable def latticeDet (n m : ℕ) (b : Fin n → (Fin m → ℝ)) : ℝ :=
  Real.sqrt ((Matrix.of b) * (Matrix.of b)ᵀ).det

noncomputable def successiveMinimum (m : ℕ) (L : Submodule ℤ (Fin m → ℝ)) (i : ℕ) : ℝ :=
  sInf {r : ℝ | i ≤ Module.finrank ℝ
    (Submodule.span ℝ ((↑L : Set (Fin m → ℝ)) ∩ Metric.closedBall 0 r))}

end LatticeBasics
