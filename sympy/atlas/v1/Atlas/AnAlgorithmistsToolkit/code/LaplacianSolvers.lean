/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/LaplacianSolvers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Matrix Finset BigOperators

namespace Matrix.IsHermitian

variable {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}

noncomputable def spectralRadius (hM : M.IsHermitian) : ℝ :=
  ⨆ i : Fin n, |hM.eigenvalues i|

end Matrix.IsHermitian

namespace An_Algorithmists_Toolkit

noncomputable def energyNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (e : Fin n → ℝ) : ℝ :=
  dotProduct e (A.mulVec e)

noncomputable def total_stretch {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (T : SimpleGraph V) : ℕ :=
  ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => T.dist u v,
    fun _ _ => SimpleGraph.dist_comm (G := T)⟩ e

noncomputable def low_stretch_exponent : ℝ := Classical.choice ⟨(1 : ℝ)⟩

end LowStretchSpanningTree

open scoped MatrixOrder ComplexOrder
open Matrix SimpleGraph Real
