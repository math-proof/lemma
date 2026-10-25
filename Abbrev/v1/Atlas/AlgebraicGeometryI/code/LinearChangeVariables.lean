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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.LinearChangeVariables
set_option maxHeartbeats 400000

open Cardinal Polynomial MvPolynomial NoetherNormalization Ideal Nat RingHom List Finset


/-- The Nagata change-of-variables `k`-algebra automorphism of
`k[x_0, …, x_n]` used to make leading coefficients units
(Lec 3, Lem 3). -/
abbrev nagataEquiv (f : MvPolynomial (Fin (n + 1)) k) :
    MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
    (t1_comp_neg f 1) (by simpa using t1_comp_neg f (-1))

