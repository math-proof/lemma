/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real


noncomputable section

open Real Finset BigOperators

namespace MultiplicativeWeights

variable {n : ℕ}

def countRounds (P : ℕ → Prop) [DecidablePred P] (t : ℕ) : ℕ :=
  ((Finset.range t).filter P).card

def expertMistakes (wrong : Fin n → ℕ → Prop) [∀ i t, Decidable (wrong i t)]
    (i : Fin n) (t : ℕ) : ℕ :=
  countRounds (wrong i) t

def weight (wrong : Fin n → ℕ → Prop) [∀ i t, Decidable (wrong i t)]
    (ε : ℝ) (i : Fin n) (t : ℕ) : ℝ :=
  (1 - ε) ^ expertMistakes wrong i t

def Φ (wrong : Fin n → ℕ → Prop) [∀ i t, Decidable (wrong i t)]
    (ε : ℝ) (t : ℕ) : ℝ :=
  ∑ i : Fin n, weight wrong ε i t

def algWrongAt (wrong : Fin n → ℕ → Prop) [∀ i t, Decidable (wrong i t)]
    (ε : ℝ) (k : ℕ) : Prop :=
  Φ wrong ε k ≤ 2 * ∑ i ∈ (Finset.univ.filter (fun i => wrong i k)),
    weight wrong ε i k

def algMistakes (wrong : Fin n → ℕ → Prop) [∀ i t, Decidable (wrong i t)]
    (ε : ℝ) (t : ℕ) : ℕ := by
  classical
  exact countRounds (algWrongAt wrong ε) t

def generalWeight (M : Fin n → P → ℝ) (ρ ε : ℝ) (outcomes : ℕ → P) (i : Fin n) : ℕ → ℝ
  | 0 => 1
  | t + 1 =>
    let m := M i (outcomes t)
    if m ≥ 0 then
      generalWeight M ρ ε outcomes i t * (1 - ε) ^ (m / ρ)
    else
      generalWeight M ρ ε outcomes i t * (1 + ε) ^ (-m / ρ)

def generalΦ (M : Fin n → P → ℝ) (ρ ε : ℝ) (outcomes : ℕ → P) (t : ℕ) : ℝ :=
  ∑ i : Fin n, generalWeight M ρ ε outcomes i t

def expertProb (M : Fin n → P → ℝ) (ρ ε : ℝ) (outcomes : ℕ → P) (i : Fin n) (t : ℕ) : ℝ :=
  generalWeight M ρ ε outcomes i t / generalΦ M ρ ε outcomes t

def expectedPenalty (M : Fin n → P → ℝ) (ρ ε : ℝ) (outcomes : ℕ → P) (t : ℕ) : ℝ :=
  ∑ i : Fin n, expertProb M ρ ε outcomes i t * M i (outcomes t)

def totalExpectedPenalty (M : Fin n → P → ℝ) (ρ ε : ℝ) (outcomes : ℕ → P) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, expectedPenalty M ρ ε outcomes t

def totalNonnegPenalty (M : Fin n → P → ℝ) (outcomes : ℕ → P) (i : Fin n) (T : ℕ) : ℝ :=
  ∑ t ∈ (Finset.range T).filter (fun t => M i (outcomes t) ≥ 0), M i (outcomes t)

def totalNegPenalty (M : Fin n → P → ℝ) (outcomes : ℕ → P) (i : Fin n) (T : ℕ) : ℝ :=
  ∑ t ∈ (Finset.range T).filter (fun t => M i (outcomes t) < 0), M i (outcomes t)

def totalExpertPenalty (M : Fin n → P → ℝ) (outcomes : ℕ → P) (i : Fin n) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, M i (outcomes t)

def expectedMistakes (wrong : Fin n → ℕ → Prop) [∀ i t, Decidable (wrong i t)]
    (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ k ∈ Finset.range T,
    (∑ i ∈ Finset.univ.filter (fun i => wrong i k), weight wrong ε i k) / Φ wrong ε k

end MultiplicativeWeights
end
