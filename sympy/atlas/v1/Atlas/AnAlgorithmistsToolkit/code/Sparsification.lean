/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Sparsification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped MatrixOrder ComplexOrder Classical
open Matrix Finset

namespace Sparsification

variable {n : Type*} {𝕜 : Type*} [RCLike 𝕜]

def GraphLoewnerLE (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] : Prop :=
  H.lapMatrix ℝ ≤ G.lapMatrix ℝ

def IsSpectralSparsifier (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (ε : ℝ) : Prop :=
  (G.lapMatrix ℝ - (1 - ε) • G'.lapMatrix ℝ).PosSemidef ∧
  ((1 + ε) • G'.lapMatrix ℝ - G.lapMatrix ℝ).PosSemidef

end GraphOrdering

section WeightedGraphOrdering

variable {V : Type*} [Fintype V] [DecidableEq V]

structure SymmWeights (V : Type*) where
  w : V → V → ℝ
  symm : ∀ i j, w i j = w j i
  diag_zero : ∀ i, w i i = 0

noncomputable def weightedLapMatrix (W : SymmWeights V) : Matrix V V ℝ :=
  Matrix.of fun i j =>
    if i = j then ∑ k : V, W.w i k
    else -W.w i j

noncomputable def cutValue (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ((Finset.univ.filter fun e : Sym2 V => e ∈ G.edgeSet).filter fun e =>
    e.out.1 ∈ S ∧ e.out.2 ∉ S ∨ e.out.1 ∉ S ∧ e.out.2 ∈ S).card

def IsNontrivialCut (S : Finset V) : Prop :=
  S.Nonempty ∧ S ≠ Finset.univ

noncomputable def minCutValue (G : SimpleGraph V) : ℕ :=
  if h : ∃ S : Finset V, IsNontrivialCut S then
    (Finset.univ.filter (fun S => IsNontrivialCut S)).image (cutValue G)
      |>.min' (by
        rw [Finset.Nonempty]
        obtain ⟨S, hS⟩ := h
        exact ⟨cutValue G S,
          Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩, rfl⟩⟩)
  else 0

noncomputable def nontrivialCutsOfValueAtMost
    (G : SimpleGraph V) (k : ℕ) : Finset (Finset V) :=
  Finset.univ.filter fun S => IsNontrivialCut S ∧ cutValue G S ≤ k

end Sparsification
