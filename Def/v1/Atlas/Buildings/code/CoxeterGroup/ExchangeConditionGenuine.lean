/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ExchangeConditionGenuine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation.Part4
import Def.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeDeletion
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Roots
open Finset BigOperators


namespace CoxeterExchangeGenuine

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The root sequence read off from a word $\omega$ and a simple root $e_s$:
the $k$-th term is the geometric image of $e_s$ under the suffix of $\omega$
of length $k$. Used to detect sign changes along the word. -/
noncomputable def rootSequence (M : CoxeterMatrix B) (word : List B) (s : B) (k : ℕ) :
    B → ℝ :=
  CoxeterGroup.wordSigma M (word.drop (word.length - k)) (CoxeterGroup.e s)

end CoxeterExchangeGenuine
