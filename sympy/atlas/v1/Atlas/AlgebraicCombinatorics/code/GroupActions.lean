/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/GroupActions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.QuotientPoset
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.QuotientPoset
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.BooleanSperner
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.BooleanUpDown
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.OrderRaisingLemma
import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.BooleanSperner
import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.BooleanUpDown
import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.OrderRaisingLemma

set_option autoImplicit false

noncomputable section

open scoped Classical Pointwise

open SpernerProperty MulAction Finset

namespace GroupActions

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

lemma out_card_of_grade (q : QuotientPoset n G) (i : ℕ)
    (hq : quotientPosetRank n G q = i) : q.out.card = i := by
  have h := @quotientPosetRank_mk n G q.out
  rw [Quotient.out_eq] at h; omega

def embedOrbits (i : ℕ)
    (f : { q : QuotientPoset n G // quotientPosetRank n G q = i } → ℝ) :
    BooleanUpDown.Level n i → ℝ :=
  fun ⟨S, hS⟩ =>
    f ⟨Quotient.mk (orbitRel G (Finset (Fin n))) S, by
      show quotientPosetRank n G _ = i
      rw [@quotientPosetRank_mk n G]; exact hS⟩

def quotientUp (i : ℕ)
    (f : { q : QuotientPoset n G // quotientPosetRank n G q = i } → ℝ) :
    { q : QuotientPoset n G // quotientPosetRank n G q = i + 1 } → ℝ :=
  fun ⟨q, hq⟩ =>
    BooleanUpDown.up i (embedOrbits i f) ⟨q.out, out_card_of_grade q (i + 1) hq⟩

def quotientUpLinear (i : ℕ) :
    ({ q : QuotientPoset n G // quotientPosetRank n G q = i } → ℝ) →ₗ[ℝ]
    ({ q : QuotientPoset n G // quotientPosetRank n G q = i + 1 } → ℝ) :=
  { toFun := quotientUp i
    map_add' := fun f g => by
      ext ⟨q, hq⟩
      simp only [quotientUp, Pi.add_apply, BooleanUpDown.up, embedOrbits]
      rw [← Finset.sum_add_distrib]
      congr 1; ext x; split_ifs <;> ring
    map_smul' := fun c f => by
      ext ⟨q, hq⟩
      simp only [quotientUp, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, BooleanUpDown.up,
        embedOrbits]
      rw [Finset.mul_sum]
      congr 1; ext x; split_ifs <;> ring }

def edgeCount (m : ℕ) : ℕ := m.choose 2

section EdgeAction

variable {m : ℕ}

def EdgeSubsets (m : ℕ) : Type :=
  { s : Finset (Fin m) // s.card = 2 }

def edgeSubsetsPowersetEquiv :
    EdgeSubsets m ≃ (Finset.univ.powersetCard 2 : Finset (Finset (Fin m))) where
  toFun := fun ⟨s, hs⟩ => ⟨s, by
    rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ s, hs⟩⟩
  invFun := fun ⟨s, hs⟩ => ⟨s, by
    rw [Finset.mem_powersetCard] at hs; exact hs.2⟩
  left_inv := fun ⟨s, _⟩ => Subtype.ext rfl
  right_inv := fun ⟨s, _⟩ => Subtype.ext rfl

noncomputable instance edgeSubsets_mulAction :
    MulAction (Equiv.Perm (Fin m)) (EdgeSubsets m) where
  smul σ e := ⟨σ • e.val, by rw [Finset.card_smul_finset]; exact e.prop⟩
  one_smul e := Subtype.ext (one_smul _ e.val)
  mul_smul σ τ e := Subtype.ext (mul_smul σ τ e.val)

noncomputable instance edgeSubsets_fintype : Fintype (EdgeSubsets m) := by
  classical
  exact Fintype.ofEquiv _ edgeSubsetsPowersetEquiv.symm

lemma card_edgeSubsets (m : ℕ) : Fintype.card (EdgeSubsets m) = edgeCount m := by
  classical
  rw [Fintype.card_congr edgeSubsetsPowersetEquiv, Fintype.card_coe, edgeCount,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

noncomputable def edgeBij (m : ℕ) : EdgeSubsets m ≃ Fin (edgeCount m) :=
  Fintype.equivFinOfCardEq (card_edgeSubsets m)

noncomputable def edgeActionHom (m : ℕ) :
    Equiv.Perm (Fin m) →* Equiv.Perm (Fin (edgeCount m)) :=
  ((edgeBij m).permCongrHom).toMonoidHom.comp
    (MulAction.toPermHom (Equiv.Perm (Fin m)) (EdgeSubsets m))

end EdgeAction

noncomputable def graphIsoGroup (m : ℕ) : Subgroup (Equiv.Perm (Fin (edgeCount m))) :=
  (edgeActionHom m).range

abbrev GraphPoset (m : ℕ) : Type :=
  QuotientPoset (edgeCount m) (graphIsoGroup m)
