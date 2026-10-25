/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section8.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.GroupTheory.QuotientGroup.Basic
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section8


namespace ExactSequence

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

attribute [instance] IntChainComplex.instAddCommGroup

/-- The induced differential on the quotient `B.X n / A.toSubgroup n`, obtained by
descending `d : B.X n →+ B.X (n - 1)` through the projection. This realizes the
existence half of Lemma 8.4 in the integer-indexed setting. -/
noncomputable def IntChainComplex.Subcomplex.quotientD
    (B : IntChainComplex) (A : B.Subcomplex) (n : ℤ) :
    B.X n ⧸ A.toSubgroup n →+ B.X (n - 1) ⧸ A.toSubgroup (n - 1) :=
  QuotientAddGroup.lift (A.toSubgroup n)
    ((QuotientAddGroup.mk' (A.toSubgroup (n - 1))).comp (B.d n))
    (fun x hx => by
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.eq_zero_iff]
      exact A.d_maps n x hx)

/-- The quotient chain complex `B / A` of an integer-indexed chain complex by a
subcomplex: in degree `n` the group is `B.X n / A.toSubgroup n`, with the induced
differential. This packages the conclusion of Lemma 8.4. -/
noncomputable def IntChainComplex.Subcomplex.quotientComplex
    (B : IntChainComplex) (A : B.Subcomplex) : IntChainComplex where
  X n := B.X n ⧸ A.toSubgroup n
  instAddCommGroup _ := inferInstance
  d n := A.quotientD B n
  d_comp_d n := A.quotientD_comp_quotientD B n

/-- Transport a chain group along an equality of indices, packaged as a group
homomorphism `C.X m →+ C.X n` when `m = n`. Used to bridge mismatched indices
when defining the homology groups. -/
def IntChainComplex.castHom (C : IntChainComplex) {m n : ℤ} (h : m = n) :
    C.X m →+ C.X n where
  toFun x := h ▸ x
  map_zero' := by subst h; rfl
  map_add' _ _ := by subst h; rfl

/-- A reindexed differential `d' : C.X (n + 1) →+ C.X n` obtained from `d` by casting
the target along `n + 1 - 1 = n`. Convenient for stating cycles/boundaries
without subtraction in the index. -/
def IntChainComplex.d' (C : IntChainComplex) (n : ℤ) : C.X (n + 1) →+ C.X n :=
  (C.castHom (show n + 1 - 1 = n by omega)).comp (C.d (n + 1))

/-- The group of `n`-cycles `Z_n(C) = ker(d : C.X n →+ C.X (n - 1))`. Generalizes
Definition 1.4 to an abstract integer-indexed chain complex. -/
def IntChainComplex.cycles (C : IntChainComplex) (n : ℤ) : AddSubgroup (C.X n) :=
  AddMonoidHom.ker (C.d n)

/-- The group of `n`-boundaries `B_n(C) = im(d : C.X (n + 1) →+ C.X n)`. Generalizes
the boundary subgroup from Definition 1.7 to an abstract integer-indexed chain complex. -/
def IntChainComplex.boundaries (C : IntChainComplex) (n : ℤ) : AddSubgroup (C.X n) :=
  AddMonoidHom.range (C.d' n)

/-- The `n`th homology group `H_n(C) = Z_n(C) / B_n(C)` of an integer-indexed chain
complex, as in Definition 1.7. -/
noncomputable def IntChainComplex.homologyGroup (C : IntChainComplex) (n : ℤ) :=
  (C.cycles n) ⧸ (C.boundaries n).addSubgroupOf (C.cycles n)

end ExactSequence
