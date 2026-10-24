/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Hastad.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.BooleanFunctions.code.PCP
import Mathlib.Data.Real.Basic

namespace Hastad

open PCP

def HasMaxSatFractionAtMost_Real (φ : ThreeSATFormula) (s : ℝ) : Prop :=
  ∀ σ : Assignment φ.numVars,
    (numSatisfied φ σ : ℝ) ≤ s * (φ.clauses.length : ℝ)

def Gap3SAT_IsNPHard_Real (s : ℝ) : Prop :=
  ∀ (L : Language), InNP L →
    ∃ (f : ∀ (n : ℕ), BinaryString n → ThreeSATFormula), IsPolyTimeReduction f ∧
      (∀ (n : ℕ) (x : BinaryString n), x ∈ L n → IsSatisfiable (f n x)) ∧
      (∀ (n : ℕ) (x : BinaryString n), x ∉ L n →
        HasMaxSatFractionAtMost_Real (f n x) s)

end Hastad
