module
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.Basic
public import Def.v1.Atlas.BooleanFunctions.code.PCP.Part5
public import Def.v1.Atlas.BooleanFunctions.code.UniqueGames.Part8
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.UniqueGames
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Talagrand
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Borel
public import Lemma.Bool.Atlas.v1.BooleanFunctions.code.InfluenceFourier
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.MultilinearExtension
public import Def.v1.Atlas.BooleanFunctions.code.MajorityStablest
public import Def.v1.Atlas.BooleanFunctions.code.Talagrand
public import Def.v1.Atlas.BooleanFunctions.code.Borel
public import Def.v1.Atlas.BooleanFunctions.code.GaussianStability.Part2
public import Def.v1.Atlas.BooleanFunctions.code.InfluenceFourier
public import Def.v1.Atlas.BooleanFunctions.code.MultilinearExtension
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Def.v1.Atlas.BooleanFunctions.code.UGCHardness
set_option maxHeartbeats 800000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Hardness.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace Hardness

open SimpleGraph

noncomputable def dinurSafraConstant : ℝ := 10 * Real.sqrt 5 - 21

def IsPolyTimeComputable {numVerts : ℕ → ℕ}
    (_ : ∀ (m : ℕ), PCP.BinaryString m → SimpleGraph (Fin (numVerts m))) : Prop :=
  ∃ (steps : ℕ → ℕ), PCP.IsPolynomial steps ∧ ∀ (m : ℕ), numVerts m ≤ steps m

def IsPolyTimeVertexCoverReduction {numVerts : ℕ → ℕ}
    (reduce : ∀ (m : ℕ), PCP.BinaryString m → SimpleGraph (Fin (numVerts m))) : Prop :=
  PCP.IsPolynomial numVerts ∧ IsPolyTimeComputable reduce

def IsNPHardToApproximateVertexCover (α : ℝ) : Prop :=
  ∀ (ε : ℝ), ε > 0 →
    ∀ (L : PCP.Language), PCP.InNP L →
      ∃ (numVerts : ℕ → ℕ)
        (reduce : ∀ (m : ℕ), PCP.BinaryString m → SimpleGraph (Fin (numVerts m)))
        (kFn : ℕ → ℕ),
        IsPolyTimeVertexCoverReduction reduce ∧
        (∀ (m : ℕ) (x : PCP.BinaryString m), x ∈ L m →
          (reduce m x).vertexCoverNum ≤ ↑(kFn m)) ∧
        (∀ (m : ℕ) (x : PCP.BinaryString m), x ∉ L m →
          (α - ε) * (↑(kFn m) : ℝ) ≤ ↑((reduce m x).vertexCoverNum.toNat))


end Hardness

open Finset BigOperators Real MeasureTheory ProbabilityTheory

namespace BooleanFourier


noncomputable def lowDegreePart {n : ℕ} (d : ℕ) (f : (Fin n → Bool) → ℝ)
    (x : Fin n → Bool) : ℝ :=
  ∑ k ∈ Finset.range (d + 1), levelComponent k f x


end BooleanFourier
