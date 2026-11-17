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
public import Def.v1.Atlas.AnAlgorithmistsToolkit.code.LatticeBasics
open Matrix BigOperators


namespace LatticeBasics

open Submodule Set

public inductive IntColumnOp (n m : ℕ) : (Fin n → (Fin m → ℝ)) → (Fin n → (Fin m → ℝ)) → Prop where
  | addMultiple (b : Fin n → (Fin m → ℝ)) (i j : Fin n) (hij : i ≠ j) (k : ℤ) :
      IntColumnOp n m b (Function.update b i (b i + (k : ℤ) • b j))
  | swap (b : Fin n → (Fin m → ℝ)) (i j : Fin n) :
      IntColumnOp n m b (b ∘ Equiv.swap i j)
  | negate (b : Fin n → (Fin m → ℝ)) (i : Fin n) :
      IntColumnOp n m b (Function.update b i (-(b i)))

public inductive IntColumnOps (n m : ℕ) : (Fin n → (Fin m → ℝ)) → (Fin n → (Fin m → ℝ)) → Prop where
  | refl (b : Fin n → (Fin m → ℝ)) : IntColumnOps n m b b
  | step {b₁ b₂ b₃ : Fin n → (Fin m → ℝ)} :
      IntColumnOps n m b₁ b₂ → IntColumnOp n m b₂ b₃ → IntColumnOps n m b₁ b₃

end LatticeBasics
