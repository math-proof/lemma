/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/SharpThreshold.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.BooleanFunctions.code.Influence
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Influence
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace BooleanFourier

open Finset

def IsIntersectingFamily {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ A B : Finset (Fin n), A ∈ F → B ∈ F → (A ∩ B).Nonempty

def IsJunta {n : ℕ} (F : Finset (Finset (Fin n))) (J : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ J ∧
    ∀ A B : Finset (Fin n), A ∩ S = B ∩ S → (A ∈ F ↔ B ∈ F)

noncomputable def muPWeight (n : ℕ) (p : ℝ) (A : Finset (Fin n)) : ℝ :=
  p ^ A.card * (1 - p) ^ (n - A.card)

noncomputable def muPMeasure {n : ℕ} (F : Finset (Finset (Fin n))) (p : ℝ) : ℝ :=
  ∑ A ∈ F, muPWeight n p A

def IsEpsCloseToIntersectingJunta {n : ℕ} (F : Finset (Finset (Fin n)))
    (p : ℝ) (ε : ℝ) (J : ℕ) : Prop :=
  ∃ G : Finset (Finset (Fin n)),
    IsIntersectingFamily G ∧ IsJunta G J ∧
      muPMeasure (F \ G) p ≤ ε

end BooleanFourier
