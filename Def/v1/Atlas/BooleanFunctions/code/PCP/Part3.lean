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
import Structure.v1.Atlas.BooleanFunctions.code.PCP.Part2


namespace PCP

def PCPVerifier.accepts {n : ℕ} (V : PCPVerifier n) (x : BinaryString n)
    (π : BinaryString V.proofLen) (r : BinaryString V.numRandom) : Bool :=
  let queriedBits : BinaryString V.numQueries := fun i => π (V.queryPositions r i)
  V.decide x r queriedBits

def PCPVerifier.hasCompleteness {n : ℕ} (V : PCPVerifier n) (L : Language)  : Prop :=
  ∀ (x : BinaryString n), x ∈ L n →
    ∃ (π : BinaryString V.proofLen), ∀ (r : BinaryString V.numRandom),
      V.accepts x π r = true

def PCPVerifier.hasSoundness {n : ℕ} (V : PCPVerifier n) (L : Language) (s : ℝ) : Prop :=
  ∀ (x : BinaryString n), x ∉ L n →
    ∀ (π : BinaryString V.proofLen),
      ((Finset.univ.filter (fun r => V.accepts x π r = true)).card : ℝ) ≤
        s * (2 : ℝ) ^ V.numRandom

def IsOLogN (f : ℕ → ℕ) : Prop :=
  ∃ (c c' : ℕ), ∀ n, f n ≤ c * Nat.log 2 n + c'

def IsO1 (f : ℕ → ℕ) : Prop :=
  ∃ (c : ℕ), ∀ n, f n ≤ c

def InPCP (L : Language) (rBound : (ℕ → ℕ) → Prop) (qBound : (ℕ → ℕ) → Prop) : Prop :=
  ∃ (r q : ℕ → ℕ), rBound r ∧ qBound q ∧
    ∃ (s : ℝ), s < 1 ∧
      ∀ (n : ℕ), ∃ (V : PCPVerifier n),
        V.numRandom = r n ∧ V.numQueries = q n ∧
        V.hasCompleteness L ∧ V.hasSoundness L s

end PCP
