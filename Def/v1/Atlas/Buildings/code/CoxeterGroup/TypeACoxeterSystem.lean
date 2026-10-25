/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeACoxeterSystem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Support
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper
open Equiv Fin


namespace SymGroupCoxeter

/-- The simple transposition $\alpha_i = (i, i+1) \in S_{n+1}$ realizing the $i$-th generator of
type $A_{n-1}$ (Section 9.6). -/
def adjTransp (n : ℕ) (i : Fin n) : Equiv.Perm (Fin (n + 1)) :=
  swap (castSucc i) (succ i)

end SymGroupCoxeter
