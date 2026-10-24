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

open Matrix BigOperators

namespace LatticeBasics

open Submodule Set

noncomputable def lattice (n m : ℕ) (b : Fin n → (Fin m → ℝ))
    (_hli : LinearIndependent ℝ b) : Submodule ℤ (Fin m → ℝ) :=
  Submodule.span ℤ (Set.range b)

def IsUnimodular {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℤ) : Prop :=
  U.det = 1 ∨ U.det = -1

def dualLattice {m : ℕ} (L : Submodule ℤ (Fin m → ℝ)) : Submodule ℤ (Fin m → ℝ) where
  carrier := {y : Fin m → ℝ | ∀ x ∈ L, ∃ k : ℤ, y ⬝ᵥ x = ↑k}
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨ka, hka⟩ := ha x hx
    obtain ⟨kb, hkb⟩ := hb x hx
    exact ⟨ka + kb, by rw [add_dotProduct, hka, hkb]; push_cast; ring⟩
  zero_mem' := by
    intro x _
    exact ⟨0, by simp [zero_dotProduct]⟩
  smul_mem' := by
    intro c y hy x hx
    obtain ⟨k, hk⟩ := hy x hx
    exact ⟨c * k, by rw [smul_dotProduct, hk]; push_cast; ring⟩

def IsDualBasis {n m : ℕ} (b b' : Fin n → (Fin m → ℝ)) : Prop :=
  (LinearIndependent ℝ b') ∧
  (Submodule.span ℝ (Set.range b') = Submodule.span ℝ (Set.range b)) ∧
  (∀ i j, dotProduct (b i) (b' j) = if i = j then 1 else 0)

def fundamentalParallelepiped (n m : ℕ) (b : Fin n → (Fin m → ℝ)) :
    Set (Fin m → ℝ) :=
  {v | ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i ∧ x i < 1) ∧ ∑ i, x i • b i = v}

inductive IntColumnOp (n m : ℕ) : (Fin n → (Fin m → ℝ)) → (Fin n → (Fin m → ℝ)) → Prop where
  | addMultiple (b : Fin n → (Fin m → ℝ)) (i j : Fin n) (hij : i ≠ j) (k : ℤ) :
      IntColumnOp n m b (Function.update b i (b i + (k : ℤ) • b j))
  | swap (b : Fin n → (Fin m → ℝ)) (i j : Fin n) :
      IntColumnOp n m b (b ∘ Equiv.swap i j)
  | negate (b : Fin n → (Fin m → ℝ)) (i : Fin n) :
      IntColumnOp n m b (Function.update b i (-(b i)))

inductive IntColumnOps (n m : ℕ) : (Fin n → (Fin m → ℝ)) → (Fin n → (Fin m → ℝ)) → Prop where
  | refl (b : Fin n → (Fin m → ℝ)) : IntColumnOps n m b b
  | step {b₁ b₂ b₃ : Fin n → (Fin m → ℝ)} :
      IntColumnOps n m b₁ b₂ → IntColumnOp n m b₂ b₃ → IntColumnOps n m b₁ b₃

noncomputable def latticeDet (n m : ℕ) (b : Fin n → (Fin m → ℝ)) : ℝ :=
  Real.sqrt ((Matrix.of b) * (Matrix.of b)ᵀ).det

noncomputable def successiveMinimum (m : ℕ) (L : Submodule ℤ (Fin m → ℝ)) (i : ℕ) : ℝ :=
  sInf {r : ℝ | i ≤ Module.finrank ℝ
    (Submodule.span ℝ ((↑L : Set (Fin m → ℝ)) ∩ Metric.closedBall 0 r))}

end LatticeBasics
