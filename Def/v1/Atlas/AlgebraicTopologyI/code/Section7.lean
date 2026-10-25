/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section7.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.CrossProductExistence
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section8
import Def.v1.Atlas.AlgebraicTopologyI.code.CrossProductExistence.Part3
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section8.Part3
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section7
open ExactSequence


namespace HomologyCrossProduct

/-- Restriction of the bidegree-`(p, q)` cross product to cycles, packaged so
that its codomain is the subgroup of cycles in `C_{p+q}`. -/
def GradedBilinearMap.cross_on_cycles
    {A B C : IntChainComplex} (μ : GradedBilinearMap A B C)
    (p q : ℤ) (a : A.cycles p) (b : B.cycles q) : C.cycles (p + q) :=
  ⟨(μ.cross p q) a.1 b.1, μ.cross_mem_cycles a.2 b.2⟩

/-- **Lemma 7.1.** Given chain complexes `A_*, B_*, C_*` and a bilinear
pairing `A_p × B_q → C_{p+q}` satisfying the Leibniz formula, the induced map
on homology is a bilinear pairing
`H_p(A) × H_q(B) → H_{p+q}(C)`. This is the descent of `cross_on_cycles` to
homology groups, using that cycles cross-multiply to cycles and that boundaries
cross-multiply (against cycles) to boundaries. -/
noncomputable def GradedBilinearMap.homology_cross_product
    {A B C : IntChainComplex} (μ : GradedBilinearMap A B C)
    (p q : ℤ) :
    A.homologyGroup p →+ (B.homologyGroup q →+ C.homologyGroup (p + q)) := by

  let BA := (A.boundaries p).addSubgroupOf (A.cycles p)
  let BB := (B.boundaries q).addSubgroupOf (B.cycles q)
  let BC := (C.boundaries (p + q)).addSubgroupOf (C.cycles (p + q))
  let mkC := QuotientAddGroup.mk' BC


  let crossFixedA : A.cycles p → B.cycles q →+ C.cycles (p + q) :=
    fun a => {
      toFun := fun b => μ.cross_on_cycles p q a b
      map_zero' := Subtype.ext (by simp [cross_on_cycles, map_zero])
      map_add' := fun b₁ b₂ => Subtype.ext (by simp [cross_on_cycles, map_add])
    }

  let phiA : A.cycles p → B.cycles q →+ C.homologyGroup (p + q) :=
    fun a => mkC.comp (crossFixedA a)

  have phiA_kills_BB : ∀ (a : A.cycles p), BB ≤ (phiA a).ker := by
    intro a b hb
    simp only [AddMonoidHom.mem_ker, phiA]
    change mkC (crossFixedA a b) = 0
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    rw [AddSubgroup.mem_addSubgroupOf] at hb ⊢
    obtain ⟨b_bar, hb_bar⟩ := hb
    show (μ.cross_on_cycles p q a b).1 ∈ C.boundaries (p + q)
    simp only [cross_on_cycles]
    rw [show b.1 = B.d' q b_bar from hb_bar.symm]
    exact μ.cross_boundary_right p q a.1 b_bar a.2

  let psiA : A.cycles p → B.homologyGroup q →+ C.homologyGroup (p + q) :=
    fun a => QuotientAddGroup.lift BB (phiA a) (phiA_kills_BB a)

  have psiA_add : ∀ (a₁ a₂ : A.cycles p),
      psiA (a₁ + a₂) = psiA a₁ + psiA a₂ := by
    intro a₁ a₂
    ext ⟨b⟩
    simp only [psiA, phiA, AddMonoidHom.add_apply]
    show mkC (crossFixedA (a₁ + a₂) b) = mkC (crossFixedA a₁ b) + mkC (crossFixedA a₂ b)
    rw [← map_add]
    congr 1
    exact Subtype.ext (by simp [crossFixedA, cross_on_cycles, map_add, AddMonoidHom.add_apply])

  have psiA_zero : psiA 0 = 0 := by
    ext ⟨b⟩
    simp only [psiA, phiA, AddMonoidHom.zero_apply]
    show mkC (crossFixedA 0 b) = 0
    have : crossFixedA 0 b = 0 :=
      Subtype.ext (by simp [crossFixedA, cross_on_cycles, map_zero, AddMonoidHom.zero_apply])
    rw [this, map_zero]

  have psiA_kills_BA : ∀ (a : A.cycles p),
      a ∈ BA → psiA a = 0 := by
    intro a ha
    rw [AddSubgroup.mem_addSubgroupOf] at ha
    obtain ⟨a_bar, ha_bar⟩ := ha
    ext ⟨b⟩
    simp only [psiA, phiA, AddMonoidHom.zero_apply]
    show mkC (crossFixedA a b) = 0
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    rw [AddSubgroup.mem_addSubgroupOf]
    show (μ.cross p q) a.1 b.1 ∈ C.boundaries (p + q)
    rw [show a.1 = A.d' p a_bar from ha_bar.symm]
    exact μ.cross_boundary_left p q a_bar b.1 b.2

  let outerHom : A.cycles p →+ (B.homologyGroup q →+ C.homologyGroup (p + q)) :=
    { toFun := psiA
      map_zero' := psiA_zero
      map_add' := psiA_add }
  exact QuotientAddGroup.lift BA outerHom (fun a ha => by
    rw [AddMonoidHom.mem_ker]
    exact psiA_kills_BA a ha)

end HomologyCrossProduct
