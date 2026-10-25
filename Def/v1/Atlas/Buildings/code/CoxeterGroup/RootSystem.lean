/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/RootSystem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation.Part4
open Finset BigOperators


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- A vector $\alpha$ is a root iff it lies in the $W$-orbit of some simple root $e_s$,
i.e. there is a word $w$ and simple $s$ with $\alpha = w \cdot e_s$. -/
def isRoot (M : CoxeterMatrix B) (α : B → ℝ) : Prop :=
  ∃ (word : List B) (s : B), α = wordSigma M word (e s)

/-- A vector is strictly positive at some coordinate: $\exists s,\, v(s) > 0$. -/
def isPositiveVec (v : B → ℝ) : Prop := ∃ s : B, v s > 0

/-- A vector is strictly negative at some coordinate: $\exists s,\, v(s) < 0$. -/
def isNegativeVec (v : B → ℝ) : Prop := ∃ s : B, v s < 0

/-- The set of simple generators $s$ such that the $s$-coordinate of $w \cdot e_s$ is strictly
negative — the simple inversions of the word. -/
def simpleInversions (M : CoxeterMatrix B) (word : List B) : Set B :=
  { s | wordSigma M word (e s) s < 0 }

/-- The action of the word $w$ on $\mathbb{R}^B$ packaged as an $\mathbb{R}$-linear map. -/
noncomputable def wordSigmaLinearMap (M : CoxeterMatrix B) (word : List B) :
    (B → ℝ) →ₗ[ℝ] (B → ℝ) where
  toFun := wordSigma M word
  map_add' := wordSigma_add M word
  map_smul' := wordSigma_smul M word

end CoxeterGroup
