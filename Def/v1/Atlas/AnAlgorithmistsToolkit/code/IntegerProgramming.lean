/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/IntegerProgramming.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.BigOperators
public import Structure.v1.Atlas.AnAlgorithmistsToolkit.code.Lattices
public import Theorem.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.Lattices

@[expose] public section

noncomputable section

open Matrix Finset InnerProductSpace

namespace IntegerProgramming

def IP.IsFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  ∃ x : Fin n → ℤ, A *ᵥ ((↑) ∘ x) ≤ b

def Lattice (n : ℕ) (b : Fin n → EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∃ c : Fin n → ℤ, y = ∑ i : Fin n, (c i : ℝ) • b i}

variable {n : ℕ}

def layerSpacingBound (m : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((m : ℝ) * ((m : ℝ) - 1)) / 4) * (2 / Real.sqrt m)

def fritzJohnRadius (n : ℕ) : ℝ := (n : ℝ) * Real.sqrt n

def layerCountBound (k : ℕ) : ℕ :=
  if k = 0 then 1
  else ⌈2 * fritzJohnRadius k / layerSpacingBound k⌉₊ + 1

def lenstraBound : ℕ → ℕ
  | 0 => 1
  | n + 1 => layerCountBound (n + 1) * lenstraBound n

def candidateBox (n : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(lenstraBound n : ℤ)) (lenstraBound n : ℤ))

end IntegerProgramming
end
