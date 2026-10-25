/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Hardness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Def.v1.Atlas.BooleanFunctions.code.PCP.Part5
import Def.v1.Atlas.BooleanFunctions.code.UniqueGames.Part8
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.UniqueGames
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Talagrand
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Borel
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.InfluenceFourier
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.MultilinearExtension
import Def.v1.Atlas.BooleanFunctions.code.MajorityStablest
import Def.v1.Atlas.BooleanFunctions.code.Talagrand
import Def.v1.Atlas.BooleanFunctions.code.Borel
import Def.v1.Atlas.BooleanFunctions.code.GaussianStability.Part2
import Def.v1.Atlas.BooleanFunctions.code.InfluenceFourier
import Def.v1.Atlas.BooleanFunctions.code.MultilinearExtension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Def.v1.Atlas.BooleanFunctions.code.UGCHardness
set_option maxHeartbeats 800000


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
