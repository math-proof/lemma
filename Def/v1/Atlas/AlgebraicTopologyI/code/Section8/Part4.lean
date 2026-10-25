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
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section8.Part2


namespace AlgebraicTopologyI

open AlgebraicTopologyI

attribute [instance] NatChainComplex.instAddCommGroup

/-- The induced differential on `B.X (n + 1) / A.toSubgroup (n + 1) →+ B.X n / A.toSubgroup n`,
defined by descending `B.d n` through the projection. This is the naturally indexed
analogue of `IntChainComplex.Subcomplex.quotientD` and the heart of Lemma 8.4. -/
noncomputable def NatChainComplex.Subcomplex.quotientD
    (B : NatChainComplex) (A : B.Subcomplex) (n : ℕ) :
    B.X (n + 1) ⧸ A.toSubgroup (n + 1) →+ B.X n ⧸ A.toSubgroup n :=
  QuotientAddGroup.lift (A.toSubgroup (n + 1))
    ((QuotientAddGroup.mk' (A.toSubgroup n)).comp (B.d n))
    (fun x hx => by
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.eq_zero_iff]
      exact A.d_maps n x hx)

/-- The quotient chain complex `B / A` of a naturally indexed chain complex by a
subcomplex: degree `n` is `B.X n / A.toSubgroup n`, with the induced differential.
This realizes Lemma 8.4 in the `ℕ`-graded setting. -/
noncomputable def NatChainComplex.Subcomplex.quotientComplex
    (B : NatChainComplex) (A : B.Subcomplex) : NatChainComplex where
  X n := B.X n ⧸ A.toSubgroup n
  instAddCommGroup _ := inferInstance
  d n := A.quotientD B n
  d_comp_d n := A.quotientD_comp_quotientD B n

/-- The singular chains of a subspace `A ⊆ X` form a subcomplex of `S_*(X)`: the image
of `S_*(A) →+ S_*(X)` is preserved by the boundary map. -/
noncomputable def relativeBoundaryMap (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) :
    RelativeSingularChains (n + 1) X A →+ RelativeSingularChains n X A :=
  QuotientAddGroup.lift _
    ((QuotientAddGroup.mk' (singularChainsInclusion n X A).range).comp (boundaryMap n X))
    (fun x hx => by
      simp only [AddMonoidHom.mem_ker]
      obtain ⟨a, ha⟩ := hx
      rw [← ha]
      have h := DFunLike.congr_fun (singularChainsInclusion_comm_boundary n X A) a
      simp only [AddMonoidHom.comp_apply] at h
      show (QuotientAddGroup.mk' _) ((boundaryMap n X) ((singularChainsInclusion (n + 1) X A) a)) = 0
      rw [h, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact ⟨boundaryMap n ↥A a, rfl⟩)

/-- The group of `n`-cycles `Z_n(C)` of a naturally indexed chain complex. In degree
`0` everything is a cycle (since `S_{-1}` is zero); in positive degrees it is the
kernel of the differential. Compare Definition 1.4. -/
def NatChainComplex.cycles (C : NatChainComplex) (n : ℕ) : AddSubgroup (C.X n) :=
  match n with
  | 0 => ⊤
  | n + 1 => AddMonoidHom.ker (C.d n)

/-- The group of `n`-boundaries `B_n(C) = im(d : C.X (n + 1) →+ C.X n)` of a
naturally indexed chain complex. -/
def NatChainComplex.boundaries (C : NatChainComplex) (n : ℕ) : AddSubgroup (C.X n) :=
  AddMonoidHom.range (C.d n)

/-- The `n`th homology group `H_n(C) = Z_n(C) / B_n(C)` of a naturally indexed chain
complex, as in Definition 1.7. -/
noncomputable def NatChainComplex.homologyGroup (C : NatChainComplex) (n : ℕ) :=
  (C.cycles n) ⧸ (C.boundaries n).addSubgroupOf (C.cycles n)

end AlgebraicTopologyI
