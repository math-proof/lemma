module
public import Theorem.v1.Atlas.AlgebraicCombinatorics.code.HasseWalks
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.HasseWalks
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.HasseWalkFormula
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkOperatorLemmas
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkCountOps
public import Instance.v1.Atlas.AlgebraicCombinatorics.code.HasseWalkFormula.Part2
public import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WalkOperatorLemmas
public import Def.v1.Atlas.AlgebraicCombinatorics.code.WalkCountOps
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option autoImplicit false
open scoped Nat
open HasseWalks


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkTypeCount.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace WalkTypeCount

def runningLevel (w : List HStep) (k : ℕ) : ℤ :=
  ((w.take k).filter (· == HStep.U)).length -
  ((w.take k).filter (· == HStep.D)).length

def IsValidStepWord (w : List HStep) (n : ℕ) : Prop :=
  runningLevel w w.length = (n : ℤ) ∧
  ∀ k : ℕ, k ≤ w.length → 0 ≤ runningLevel w k

def walkTypeCount (w : List HStep) (lam : YoungDiagram) : ℕ := by
  classical
  exact Nat.card (HasseWalk w ⊥ lam)

def downPositions (w : List HStep) : Finset (Fin w.length) :=
  Finset.univ.filter (fun i => w[i] = HStep.D)

def numDRight (w : List HStep) (i : Fin w.length) : ℕ :=
  ((w.take i.val).filter (· == HStep.D)).length

def numURight (w : List HStep) (i : Fin w.length) : ℕ :=
  ((w.take i.val).filter (· == HStep.U)).length

def downStepProduct (w : List HStep) : ℤ :=
  ∏ i ∈ downPositions w,
    ((numURight w i : ℤ) - (numDRight w i : ℤ))

def applyStepWord : List HStep → (YoungDiagram →₀ ℤ) → (YoungDiagram →₀ ℤ)
  | [], f => f
  | HStep.U :: rest, f => applyStepWord rest (WalkCountFormula.liftU f)
  | HStep.D :: rest, f => applyStepWord rest (WalkCountFormula.liftD f)

def downFactor : List HStep → ℕ → ℤ
  | [], _ => 1
  | HStep.U :: rest, m => downFactor rest (m + 1)
  | HStep.D :: rest, m => (m : ℤ) * downFactor rest (m - 1)

def finalLevel : List HStep → ℕ → ℕ
  | [], m => m
  | HStep.U :: rest, m => finalLevel rest (m + 1)
  | HStep.D :: rest, m => finalLevel rest (m - 1)

end WalkTypeCount
end
