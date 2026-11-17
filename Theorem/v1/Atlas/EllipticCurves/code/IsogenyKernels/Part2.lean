/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IsogenyKernels.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Wronskian
public import Mathlib.Tactic.LinearCombination
public import Def.v1.Atlas.EllipticCurves.code.IsogenyKernels.Part2
open Polynomial

public section

variable {E : ShortWeierstrassCurve k}


/-- Unfolding $t_Q$. -/
@[simp] lemma AffinePoint.tQ_val (Q : AffinePoint E) :
    Q.tQ = 3 * Q.x ^ 2 + E.A := rfl

/-- Unfolding $u_Q$. -/
@[simp] lemma AffinePoint.uQ_val (Q : AffinePoint E) :
    Q.uQ = 2 * Q.y ^ 2 := rfl

/-- Unfolding $w_Q$. -/
@[simp] lemma AffinePoint.wQ_val (Q : AffinePoint E) :
    Q.wQ = Q.uQ + Q.tQ * Q.x := rfl

