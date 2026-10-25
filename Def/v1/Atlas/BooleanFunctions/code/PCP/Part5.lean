/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/PCP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Structure.v1.Atlas.BooleanFunctions.code.PCP.Part4


namespace PCP

def numSatisfied (φ : ThreeSATFormula) (σ : Assignment φ.numVars) : ℕ :=
  (φ.clauses.filter (·.satisfiedBy σ = true)).length

def IsSatisfiable (φ : ThreeSATFormula) : Prop :=
  ∃ σ : Assignment φ.numVars, ∀ c ∈ φ.clauses, c.satisfiedBy σ = true

def HasMaxSatFractionAtMost (φ : ThreeSATFormula) (s : ℝ) : Prop :=
  ∀ σ : Assignment φ.numVars, (numSatisfied φ σ : ℝ) ≤ s * (φ.clauses.length : ℝ)

opaque IsPolyTimeReduction : (∀ (n : ℕ), BinaryString n → ThreeSATFormula) → Prop

def Gap3SAT_IsNPHard (s : ℝ) : Prop :=
  ∀ (L : Language), InNP L →
    ∃ (f : ∀ (n : ℕ), BinaryString n → ThreeSATFormula), IsPolyTimeReduction f ∧
      (∀ (n : ℕ) (x : BinaryString n), x ∈ L n → IsSatisfiable (f n x)) ∧
      (∀ (n : ℕ) (x : BinaryString n), x ∉ L n →
        HasMaxSatFractionAtMost (f n x) s)


end PCP
