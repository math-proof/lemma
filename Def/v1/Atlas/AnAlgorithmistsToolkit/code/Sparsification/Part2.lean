/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Sparsification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Data.Fintype.Card
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Structure.v1.Atlas.AnAlgorithmistsToolkit.code.Sparsification

@[expose] public section

open scoped MatrixOrder ComplexOrder Classical
open Matrix Finset


section WeightedGraphOrdering

variable {V : Type*} [Fintype V] [DecidableEq V]

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

end WeightedGraphOrdering
