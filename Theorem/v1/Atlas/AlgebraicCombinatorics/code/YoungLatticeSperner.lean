/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLatticeSperner.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.QuotientIsoLmn.Part7
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.QuotientIsoLmn
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.GroupActions
import Abbrev.v1.Atlas.AlgebraicCombinatorics.code.GroupActions
import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungLatticeSperner
set_option autoImplicit false


noncomputable section

open scoped Classical Pointwise

open SpernerProperty YoungLattice YoungLattice.Lmn

open QuotientIsoLmn GroupActions WreathOrbits Finset MulAction

namespace YoungLattice.Lmn

variable {m n : ℕ}

lemma wreathElemToPerm_apply (g : WreathElem m n) (p : Fin m × Fin n) :
    wreathElemToPerm g p = g.actOn p := rfl

lemma sum_rowSize_eq_card (S : Finset (Fin m × Fin n)) :
    ∑ i : Fin m, rowSize S i = S.card := by
  simp only [rowSize]
  have hdisj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun i => S.filter (fun p => p.1 = i)) := by
    intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_filter]
    intro ⟨_, _⟩ _ ha hj
    exact hij (ha ▸ hj)
  rw [← Finset.card_biUnion hdisj]
  congr 1
  ext ⟨i, j⟩
  simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
  constructor
  · rintro ⟨_, h1, _⟩; exact h1
  · intro h; exact ⟨i, h, rfl⟩

lemma image_finProdFinEquiv_actOnSet (g : WreathElem m n)
    (S : Finset (Fin m × Fin n)) :
    (g.actOnSet S).image finProdFinEquiv =
    (finProdFinEquiv.permCongr (wreathElemToPerm g)) •
      (S.image finProdFinEquiv) := by
  simp only [Finset.smul_finset_def, WreathElem.actOnSet, Equiv.Perm.smul_def]
  rw [Finset.image_image, Finset.image_image]
  congr 1; funext x
  simp only [Function.comp, Equiv.permCongr_apply, wreathElemToPerm_apply,
    Equiv.symm_apply_apply]

lemma smul_image_symm_eq_actOnSet (g : WreathElem m n)
    (A : Finset (Fin (m * n))) :
    ((finProdFinEquiv.permCongr (wreathElemToPerm g)) • A).image
      finProdFinEquiv.symm =
    g.actOnSet (A.image finProdFinEquiv.symm) := by
  simp only [Finset.smul_finset_def, WreathElem.actOnSet, Equiv.Perm.smul_def]
  rw [Finset.image_image, Finset.image_image]
  congr 1; funext x
  simp only [Function.comp, Equiv.permCongr_apply, wreathElemToPerm_apply,
    Equiv.symm_apply_apply]

lemma wreathSubgroup_orbit_of_sameOrbit (S T : Finset (Fin m × Fin n))
    (h : WreathOrbits.SameOrbit S T) :
    ∃ (g : ↥(wreathSubgroup m n)),
      g • (S.image finProdFinEquiv) = T.image finProdFinEquiv := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨⟨_, Subgroup.subset_closure ⟨w, rfl⟩⟩,
    (image_finProdFinEquiv_actOnSet w S).symm⟩

set_option maxHeartbeats 1600000 in
lemma sameOrbit_of_wreathSubgroup_orbit
    (A : Finset (Fin (m * n)))
    (g : ↥(wreathSubgroup m n)) :
    WreathOrbits.SameOrbit (A.image finProdFinEquiv.symm)
      ((g • A).image finProdFinEquiv.symm) := by
  suffices key : ∀ (π : Equiv.Perm (Fin (m * n))) (_ : π ∈ wreathSubgroup m n)
      (C : Finset (Fin (m * n))),
      rowSizeMultiset ((π • C).image finProdFinEquiv.symm) =
        rowSizeMultiset (C.image finProdFinEquiv.symm) by
    exact (sameOrbit_iff_rowSizeMultiset_eq _ _).mpr (key g.1 g.2 A).symm
  intro π hπ
  induction hπ using Subgroup.closure_induction with
  | mem x hx =>
    intro C
    obtain ⟨w, rfl⟩ := hx
    rw [smul_image_symm_eq_actOnSet]
    exact ((sameOrbit_iff_rowSizeMultiset_eq _ _).mp ⟨w, rfl⟩).symm
  | one => intro C; simp only [one_smul]
  | mul x y _ _ ihx ihy =>
    intro C; rw [mul_smul, ihx (y • C), ihy C]
  | inv x _ ih =>
    intro C
    specialize ih (x⁻¹ • C)
    rw [smul_inv_smul] at ih
    exact ih.symm

end YoungLattice.Lmn
end
