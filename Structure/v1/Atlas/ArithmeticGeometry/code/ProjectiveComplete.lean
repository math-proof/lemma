/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.ArithmeticGeometry.code.CompletenessValuationCriterion.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CompletenessValuationCriterion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
universe u

open AlgebraicGeometry


/-- A projective variety structure on $V$: a choice of dimension $n$ and homogeneous coordinates $X_0, \dots, X_n \in K(Z)^\times$ (none vanishing) on every subvariety $Z$ of $V$. -/
structure IsProjectiveVariety {k : Type u} [Field k] (V : AlgVariety k) where
  n : ℕ
  homogCoords : (Z : SubvarietyOf V) → Fin (n + 1) → Z.toVariety.functionField
  homogCoords_ne_zero : ∀ (Z : SubvarietyOf V) (i : Fin (n + 1)),
    homogCoords Z i ≠ 0

