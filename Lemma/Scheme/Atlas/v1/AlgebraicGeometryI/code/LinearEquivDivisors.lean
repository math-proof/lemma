import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.LinearEquivDivisors
open LinearEquivDivisors
open scoped nonZeroDivisors


namespace LinearEquivDivisors

/--
[WeilDivisor.degree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma WeilDivisor.degree_zero
-- imply
  WeilDivisor.degree (0 : WeilDivisorGroup Y) = 0 := by
-- proof
  simp [WeilDivisor.degree, Finsupp.sum_zero_index]

end LinearEquivDivisors

namespace LinearEquivDivisors

/--
[WeilDivisor.degree_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma WeilDivisor.degree_add
  [DecidableEq Y]
  {D₁ D₂ : WeilDivisorGroup Y} :
-- imply
  WeilDivisor.degree (D₁ + D₂) = WeilDivisor.degree D₁ + WeilDivisor.degree D₂ := by
-- proof
  simp only [WeilDivisor.degree]
  rw [Finsupp.sum_add_index (by simp) (by intros; ring)]

end LinearEquivDivisors

namespace LinearEquivDivisors

/--
[WeilDivisor.degree_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma WeilDivisor.degree_neg
  {D : WeilDivisorGroup Y} :
-- imply
  WeilDivisor.degree (-D) = -WeilDivisor.degree D := by
-- proof
  simp only [WeilDivisor.degree]
  rw [Finsupp.sum_neg_index (by simp)]
  simp [Finsupp.sum, Finset.sum_neg_distrib]

end LinearEquivDivisors

namespace LinearEquivDivisors

/--
[WeilDivisor.degree_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma WeilDivisor.degree_sub
  [DecidableEq Y]
  {D₁ D₂ : WeilDivisorGroup Y} :
-- imply
  WeilDivisor.degree (D₁ - D₂) = WeilDivisor.degree D₁ - WeilDivisor.degree D₂ := by
-- proof
  rw [sub_eq_add_neg, degree_add, degree_neg, sub_eq_add_neg]

end LinearEquivDivisors

namespace LinearEquivDivisors

/--
[WeilDivisor.degree_eq_of_linearlyEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma WeilDivisor.degree_eq_of_linearlyEquiv
  [DecidableEq Y]
  {P : PrincipalDivisors Y}
  {D₁ D₂ : WeilDivisorGroup Y}
-- given
  (hP : ∀ D ∈ P, WeilDivisor.degree D = 0)
  (h : WeilLinearlyEquivalent P D₁ D₂) :
-- imply
  WeilDivisor.degree D₁ = WeilDivisor.degree D₂ := by
-- proof
  have := hP _ h
  rw [degree_sub] at this
  omega

end LinearEquivDivisors

namespace LinearEquivDivisors

/--
[mem_completeLinearSystem_isEffective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma mem_completeLinearSystem_isEffective
  [DecidableEq Y]
  {P : PrincipalDivisors Y}
  {D D' : WeilDivisorGroup Y}
-- given
  (h : D' ∈ completeLinearSystem P D) :
-- imply
  WeilDivisor.IsEffective D' :=
-- proof
  h.1

end LinearEquivDivisors

namespace LinearEquivDivisors

/--
[mem_completeLinearSystem_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma mem_completeLinearSystem_equiv
  [DecidableEq Y]
  {P : PrincipalDivisors Y}
  {D D' : WeilDivisorGroup Y}
-- given
  (h : D' ∈ completeLinearSystem P D) :
-- imply
  WeilLinearlyEquivalent P D' D :=
-- proof
  h.2

end LinearEquivDivisors

namespace LinearEquivDivisors

/--
[self_mem_completeLinearSystem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma self_mem_completeLinearSystem
  [DecidableEq Y]
  {P : PrincipalDivisors Y}
  {D : WeilDivisorGroup Y}
-- given
  (hD : WeilDivisor.IsEffective D) :
-- imply
  D ∈ completeLinearSystem P D :=
-- proof
  ⟨hD, WeilLinearlyEquivalent.refl P D⟩

end LinearEquivDivisors

namespace LinearEquivDivisors

/--
[completeLinearSystem_top_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma completeLinearSystem_top_eq
  [DecidableEq Y]
  {D : WeilDivisorGroup Y} :
-- imply
  completeLinearSystem ⊤ D = {D' | WeilDivisor.IsEffective D'} := by
-- proof
  ext D'
  simp [completeLinearSystem, WeilLinearlyEquivalent]

end LinearEquivDivisors

namespace LinearEquivDivisors

/--
[completeLinearSystem_bot_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma completeLinearSystem_bot_eq
  [DecidableEq Y]
  {D : WeilDivisorGroup Y} :
-- imply
  completeLinearSystem ⊥ D = {D' | WeilDivisor.IsEffective D' ∧ D' = D} := by
-- proof
  ext D'
  simp [completeLinearSystem, WeilLinearlyEquivalent, AddSubgroup.mem_bot, sub_eq_zero]

end LinearEquivDivisors

namespace LinearEquivDivisors

/--
[cartierLinearlyEquivalent_equivalence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma cartierLinearlyEquivalent_equivalence
  [DecidableEq Y]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A] :
-- imply
  Equivalence (fun I J : (Ideal A)⁰ => CartierDivisor.LinearlyEquivalent A I J) where refl _ :=
-- proof
  rfl
    symm h := h.symm
    trans h₁ h₂ := h₁.trans h₂

end LinearEquivDivisors

namespace LinearEquivDivisors

/--
[cartierDivisor_principal_iff_trivialClass](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma cartierDivisor_principal_iff_trivialClass
  [DecidableEq Y]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  {I : Ideal A}
-- given
  (hI : I ∈ (Ideal A)⁰) :
-- imply
  ClassGroup.mk0 ⟨I, hI⟩ = 1 ↔ Submodule.IsPrincipal I :=
-- proof
  ClassGroup.mk0_eq_one_iff hI

end LinearEquivDivisors

namespace LinearEquivDivisors

/--
[completeLinearSystemDim_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma completeLinearSystemDim_eq
  [DecidableEq Y]
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Module.Finite k V] :
-- imply
  completeLinearSystemDim k V = (Module.finrank k V : ℤ) - 1 :=
-- proof
  rfl

end LinearEquivDivisors

namespace LinearEquivDivisors

/--
[completeLinearSystemDim_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma completeLinearSystemDim_nonneg
  [DecidableEq Y]
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Module.Finite k V]
-- given
  (hV : 0 < Module.finrank k V) :
-- imply
  0 ≤ completeLinearSystemDim k V := by
-- proof
  simp [completeLinearSystemDim]
  omega

end LinearEquivDivisors

namespace LinearEquivDivisors

/--
[completeLinearSystem_nonempty_of_nontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma completeLinearSystem_nonempty_of_nontrivial
  [DecidableEq Y]
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Nontrivial V] :
-- imply
  Nonempty (Projectivization k V) :=
-- proof
  inferInstance

end LinearEquivDivisors

namespace LinearEquivDivisors

/--
[WeilDivisor.IsEffective_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma WeilDivisor.IsEffective_zero
  [DecidableEq Y] :
-- imply
  WeilDivisor.IsEffective (0 : WeilDivisorGroup Y) :=
-- proof
  fun _ => le_refl 0

end LinearEquivDivisors

namespace LinearEquivDivisors

/--
[WeilDivisor.IsEffective_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
lemma WeilDivisor.IsEffective_add
  [DecidableEq Y]
  {D₁ D₂ : WeilDivisorGroup Y}
-- given
  (h₁ : WeilDivisor.IsEffective D₁)
  (h₂ : WeilDivisor.IsEffective D₂) :
-- imply
  WeilDivisor.IsEffective (D₁ + D₂) :=
-- proof
  fun y => by simp [Finsupp.add_apply]; exact add_nonneg (h₁ y) (h₂ y)
end LinearEquivDivisors


/--
[weilLinearlyEquivalent_equivalence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
private lemma weilLinearlyEquivalent_equivalence_eq
  {P : PrincipalDivisors Y} :
-- imply
  Equivalence (WeilLinearlyEquivalent P) where refl D := by
-- proof
  apply LinearEquivDivisors.weilLinearlyEquivalent_equivalence P

/--
[WeilLinearlyEquivalent.refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
private lemma refl_eq
  {P : PrincipalDivisors Y}
  {D : WeilDivisorGroup Y} :
-- imply
  WeilLinearlyEquivalent P D D := by
-- proof
  apply LinearEquivDivisors.WeilLinearlyEquivalent.refl P D

/--
[WeilLinearlyEquivalent.symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
private lemma symm_eq
  {P : PrincipalDivisors Y}
  {D₁ D₂ : WeilDivisorGroup Y}
-- given
  (h : WeilLinearlyEquivalent P D₁ D₂) :
-- imply
  WeilLinearlyEquivalent P D₂ D₁ := by
-- proof
  apply LinearEquivDivisors.WeilLinearlyEquivalent.symm P h

/--
[WeilLinearlyEquivalent.trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean)
-/
@[path]
private lemma trans_eq
  {P : PrincipalDivisors Y}
  {D₁ D₂ D₃ : WeilDivisorGroup Y}
-- given
  (h₁ : WeilLinearlyEquivalent P D₁ D₂)
  (h₂ : WeilLinearlyEquivalent P D₂ D₃) :
-- imply
  WeilLinearlyEquivalent P D₁ D₃ := by
-- proof
  apply LinearEquivDivisors.WeilLinearlyEquivalent.trans P h₁ h₂


-- created on 2026-10-23
