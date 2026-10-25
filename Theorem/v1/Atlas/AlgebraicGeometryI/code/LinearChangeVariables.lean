/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearChangeVariables.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.NoetherNormalization
set_option maxHeartbeats 400000

open Cardinal Polynomial MvPolynomial NoetherNormalization Ideal Nat RingHom List Finset


/-- Composing the Nagata substitution with its negative inverse yields
the identity. -/
lemma t1_comp_neg (f : MvPolynomial (Fin (n + 1)) k) (c : k) :
    (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]; ext i v; cases i using Fin.cases <;> simp

