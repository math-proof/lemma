/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
set_option linter.unusedSectionVars false


/-- A *BN-pair* (Tits system) on a group $G$ relative to a Coxeter matrix $M$:
data of subgroups $B, N, T = B \cap N$ together with a surjection $\pi : N \twoheadrightarrow W = M.\text{Group}$
whose kernel is $T$, such that $B \cup N$ generates $G$. The Coxeter group $W = N/T$ acts as
the *Weyl group*; the cells $BwB$ partition $G$ (Bruhat decomposition). -/
structure BNPair (G : Type*) [Group G] {B_idx : Type*}
    (M : CoxeterMatrix B_idx) where
  B : Subgroup G
  N : Subgroup G
  T : Subgroup G
  T_eq : T = B ⊓ N
  π : N →* M.Group
  π_surj : Function.Surjective π
  π_ker : ∀ n : N, π n = 1 ↔ (n : G) ∈ T
  generates : Subgroup.closure ((B : Set G) ∪ (N : Set G)) = ⊤

