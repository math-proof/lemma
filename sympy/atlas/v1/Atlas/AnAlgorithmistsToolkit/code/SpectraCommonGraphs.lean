/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace SimpleGraph

variable {V : Type*} {W : Type*}

abbrev cartesianProduct (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V × W) :=
  G □ H

end SimpleGraph

namespace SpectraCommonGraphs

open Real SimpleGraph Matrix

noncomputable section

abbrev ringGraph (n : ℕ) : SimpleGraph (Fin n) := SimpleGraph.cycleGraph n

def ringEigenvalue (n : ℕ) (k : ℕ) : ℝ :=
  2 - 2 * Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ))

def cosEigenvector (n : ℕ) (k : ℕ) (u : Fin n) : ℝ :=
  Real.cos (2 * Real.pi * (k : ℝ) * (u.val : ℝ) / (n : ℝ))

def sinEigenvector (n : ℕ) (k : ℕ) (u : Fin n) : ℝ :=
  Real.sin (2 * Real.pi * (k : ℝ) * (u.val : ℝ) / (n : ℝ))

def vecTensor {V W : Type*} (v : V → ℝ) (w : W → ℝ) : V × W → ℝ :=
  fun p => v p.1 * w p.2

open SimpleGraph in
instance boxProd_decidableAdj
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj := by
  intro ⟨v₁, w₁⟩ ⟨v₂, w₂⟩; rw [SimpleGraph.boxProd_adj]; infer_instance
