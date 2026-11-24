module
public import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLatticeSperner
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.QBinomial
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.GroupActions
public import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungLatticeSperner.Part3
public import Def.v1.Atlas.AlgebraicCombinatorics.code.QBinomial.Part2
public import Abbrev.v1.Atlas.AlgebraicCombinatorics.code.GroupActions
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic
public import Def.v1.Atlas.AlgebraicCombinatorics.code.SubsetSum
set_option autoImplicit false
open SpernerProperty YoungLattice YoungLattice.Lmn Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace SubsetSum

lemma strictMono_fin_add_le {k : ℕ} {s : Fin k → ℕ} (hs : StrictMono s)
    (a b : Fin k) (hab : a ≤ b) : s a + (b.val - a.val) ≤ s b := by
  suffices key : ∀ (d : ℕ) (c e : Fin k), c.val + d = e.val → s c + d ≤ s e by
    exact key (b.val - a.val) a b (by omega)
  intro d
  induction d with
  | zero => intro c e h; have : c = e := Fin.ext (by omega); subst this; exact le_refl _
  | succ d ih =>
    intro c e hce
    let f : Fin k := ⟨e.val - 1, by omega⟩
    have h1 : s c + d ≤ s f := ih c f (by simp [f]; omega)
    have h2 : s f + 1 ≤ s e := Nat.succ_le_of_lt (hs (Fin.mk_lt_mk.mpr (by omega)))
    omega

end SubsetSum
