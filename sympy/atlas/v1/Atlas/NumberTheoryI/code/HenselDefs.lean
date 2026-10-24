/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/HenselDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination

open Polynomial

section FormalDerivative

variable {R : Type*}

def IsSimpleRoot (f : R[X]) (a : R) : Prop :=
  f.eval a = 0 ∧ (derivative f).eval a ≠ 0

end SimpleRoot
