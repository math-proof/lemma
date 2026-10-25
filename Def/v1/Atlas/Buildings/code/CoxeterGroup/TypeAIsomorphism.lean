/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAIsomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.PresentedGroup
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper
open Equiv Equiv.Perm Function Set


namespace SymmetricCoxeter

/-- The adjacent transposition $\alpha_i = (i, i+1) \in S_{n+1}$. -/
def adjTransposition (n : ℕ) (i : Fin n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap (Fin.castSucc i) (Fin.succ i)

end SymmetricCoxeter
