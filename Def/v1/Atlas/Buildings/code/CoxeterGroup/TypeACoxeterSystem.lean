/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeACoxeterSystem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Coxeter.Matrix
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Support
public import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper

@[expose] public section

open Equiv Fin


namespace SymGroupCoxeter

/-- The simple transposition $\alpha_i = (i, i+1) \in S_{n+1}$ realizing the $i$-th generator of
type $A_{n-1}$ (Section 9.6). -/
def adjTransp (n : ℕ) (i : Fin n) : Equiv.Perm (Fin (n + 1)) :=
  swap (castSucc i) (succ i)

end SymGroupCoxeter
