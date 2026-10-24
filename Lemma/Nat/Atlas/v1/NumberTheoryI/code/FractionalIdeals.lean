import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.FractionalIdeals
open nonZeroDivisors FractionalIdeal


/--
[isFractional_iff_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma isFractional_iff_fg
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I : Submodule A K} :
-- imply
  IsFractional A⁰ I ↔ I.FG := by
-- proof
  constructor
  · intro hI
    exact FractionalIdeal.fg_of_isNoetherianRing (le_refl A⁰) ⟨I, hI⟩
  · exact FractionalIdeal.isFractional_of_fg

/--
[submodule_fg_iff_isFractional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma submodule_fg_iff_isFractional
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I : Submodule A K} :
-- imply
  I.FG ↔ IsFractional A⁰ I := by
-- proof
  constructor
  · exact FractionalIdeal.isFractional_of_fg
  · intro hI
    exact FractionalIdeal.fg_of_isNoetherianRing (le_refl A⁰) ⟨I, hI⟩

/--
[ideal_coe_fractionalIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma ideal_coe_fractionalIdeal
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I : Ideal A} :
-- imply
  ∃ J : FractionalIdeal A⁰ K, (J : Submodule A K) = IsLocalization.coeSubmodule K I :=
-- proof
  ⟨↑I, rfl⟩

/--
[fractionalIdeal_exists_eq_spanSingleton_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma fractionalIdeal_exists_eq_spanSingleton_mul
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {J : FractionalIdeal A⁰ K} :
-- imply
  ∃ (a : A) (I : Ideal A), a ≠ 0 ∧ J = FractionalIdeal.spanSingleton A⁰ ((algebraMap A K a)⁻¹) * ↑I :=
-- proof
  FractionalIdeal.exists_eq_spanSingleton_mul J

/--
[Definition_2_13](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma Definition_2_13
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I : Submodule A K} :
-- imply
  IsFractional A⁰ I ↔ I.FG :=
-- proof
  isFractional_iff_fg A K I

/--
[Lemma_2_14](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma Lemma_2_14
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I : Submodule A K} :
-- imply
  I.FG ↔ IsFractional A⁰ I :=
-- proof
  submodule_fg_iff_isFractional A K I

/--
[Corollary_2_16](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma Corollary_2_16
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {J : FractionalIdeal A⁰ K} :
-- imply
  ∃ (a : A) (I : Ideal A), a ≠ 0 ∧ J = FractionalIdeal.spanSingleton A⁰ ((algebraMap A K a)⁻¹) * ↑I :=
-- proof
  fractionalIdeal_exists_eq_spanSingleton_mul A K J
section PrincipalFractionalIdeals
variable (A : Type*) [CommRing A] [IsDomain A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

/--
[fractionalIdeal_isPrincipal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma fractionalIdeal_isPrincipal_iff
  {A : Type*}
  [CommRing A]
  {I : FractionalIdeal A⁰ K} :
-- imply
  (I : Submodule A K).IsPrincipal ↔ ∃ x : K, I = FractionalIdeal.spanSingleton A⁰ x :=
-- proof
  FractionalIdeal.isPrincipal_iff I

/--
[Definition_2_17](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma Definition_2_17
  {A : Type*}
  [CommRing A]
  {I : FractionalIdeal A⁰ K} :
-- imply
  (I : Submodule A K).IsPrincipal ↔ ∃ x : K, I = FractionalIdeal.spanSingleton A⁰ x :=
-- proof
  fractionalIdeal_isPrincipal_iff A K I

/--
[mem_principalFractionalIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma mem_principalFractionalIdeal
  {A : Type*}
  [CommRing A]
  {x y : K} :
-- imply
  y ∈ principalFractionalIdeal A K x ↔ ∃ a : A, a • x = y :=
-- proof
  FractionalIdeal.mem_spanSingleton A⁰

/--
[colonIdeal_isFractional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma colonIdeal_isFractional
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I J : FractionalIdeal A⁰ K}
-- given
  (hJ : J ≠ 0) :
-- imply
  IsFractional A⁰ ((I : Submodule A K) / (J : Submodule A K)) :=
-- proof
  FractionalIdeal.isFractional_div_of_ne_zero hJ

/--
[Lemma_2_18_isFractional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma Lemma_2_18_isFractional
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I J : FractionalIdeal A⁰ K}
-- given
  (hJ : J ≠ 0) :
-- imply
  IsFractional A⁰ ((I : Submodule A K) / (J : Submodule A K)) :=
-- proof
  colonIdeal_isFractional A K I J hJ

/--
[colonIdeal_isFractionalIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma colonIdeal_isFractionalIdeal
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I J : FractionalIdeal A⁰ K}
-- given
  (hJ : J ≠ 0) :
-- imply
  ∃ Q : FractionalIdeal A⁰ K, ∀ x : K, x ∈ (Q : Submodule A K) ↔ ∀ y ∈ (J : Submodule A K), x * y ∈ (I : Submodule A K) :=
-- proof
  ⟨I / J, fun _ => FractionalIdeal.mem_div_iff_of_ne_zero hJ⟩

/--
[Lemma_2_18](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma Lemma_2_18
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I J : FractionalIdeal A⁰ K}
-- given
  (hJ : J ≠ 0) :
-- imply
  ∃ Q : FractionalIdeal A⁰ K, ∀ x : K, x ∈ (Q : Submodule A K) ↔ ∀ y ∈ (J : Submodule A K), x * y ∈ (I : Submodule A K) :=
-- proof
  colonIdeal_isFractionalIdeal A K I J hJ
namespace FractionalIdeal
section
variable {A : Type*} [CommRing A] [IsDomain A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

namespace FractionalIdeal

/--
[isInvertible_iff_exists_mul_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma isInvertible_iff_exists_mul_eq_one
  [CommRing A]
  [IsDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I : FractionalIdeal A⁰ K} :
-- imply
  IsInvertible I ↔ ∃ J : FractionalIdeal A⁰ K, I * J = 1 :=
-- proof
  Iff.rfl

end FractionalIdeal

namespace FractionalIdeal

/--
[Definition_2_19](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma Definition_2_19
  [CommRing A]
  [IsDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I : FractionalIdeal A⁰ K} :
-- imply
  IsInvertible I ↔ ∃ J : FractionalIdeal A⁰ K, I * J = 1 :=
-- proof
  isInvertible_iff_exists_mul_eq_one I

end FractionalIdeal

namespace FractionalIdeal

/--
[isInvertible_iff_mul_inv_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma isInvertible_iff_mul_inv_cancel
  [CommRing A]
  [IsDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I : FractionalIdeal A⁰ K} :
-- imply
  IsInvertible I ↔ I * I⁻¹ = 1 :=
-- proof
  (FractionalIdeal.mul_inv_cancel_iff K).symm

end FractionalIdeal

namespace FractionalIdeal

/--
[IsInvertible.inv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma IsInvertible.inv_eq
  [CommRing A]
  [IsDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I J : FractionalIdeal A⁰ K}
-- given
  (h : I * J = 1) :
-- imply
  J = I⁻¹ :=
-- proof
  FractionalIdeal.right_inverse_eq K I J h
end
section

end FractionalIdeal

namespace FractionalIdeal

/--
[isInvertible_iff_isUnit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma isInvertible_iff_isUnit
  [CommRing A]
  [Field K]
  [Algebra A K]
  {I : FractionalIdeal A⁰ K} :
-- imply
  IsInvertible I ↔ IsUnit I :=
-- proof
  isUnit_iff_exists_inv.symm

end FractionalIdeal

namespace FractionalIdeal

/--
[IsInvertible.inv_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma IsInvertible.inv_unique
  [CommRing A]
  [Field K]
  [Algebra A K]
  {I J J' : FractionalIdeal A⁰ K}
-- given
  (hJ : I * J = 1)
  (hJ' : I * J' = 1) :
-- imply
  J = J' := by
-- proof
  calc J = J * 1 := (mul_one J).symm
    _ = J * (I * J') := by rw [hJ']
    _ = (J * I) * J' := (mul_assoc J I J').symm
    _ = (I * J) * J' := by rw [mul_comm J I]
    _ = 1 * J' := by rw [hJ]
    _ = J' := one_mul J'
end
section


namespace FractionalIdeal

/--
[isInvertible_iff_mul_inv_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma isInvertible_iff_mul_inv_eq_one
  [CommRing A]
  [IsDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I : FractionalIdeal A⁰ K} :
-- imply
  IsInvertible I ↔ I * I⁻¹ = 1 := by
-- proof
  constructor
  ·
    rintro ⟨J, hJ⟩
    have hI : I ≠ 0 := ne_zero_of_mul_eq_one I J hJ
    have hJ_le : J ≤ I⁻¹ := by
      rw [FractionalIdeal.inv_eq]
      exact (le_div_iff_of_ne_zero hI).mpr fun y hy x hx => by
        rw [mul_comm]; exact hJ ▸ mul_mem_mul hx hy
    apply le_antisymm
    ·
      rw [FractionalIdeal.inv_eq]; exact mul_one_div_le_one
    ·
      calc (1 : FractionalIdeal A⁰ K) = I * J := hJ.symm
        _ ≤ I * I⁻¹ := by gcongr
  ·
    exact fun h => ⟨I⁻¹, h⟩

end FractionalIdeal

namespace FractionalIdeal

/--
[Lemma_2_20](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma Lemma_2_20
  [CommRing A]
  [IsDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {I : FractionalIdeal A⁰ K} :
-- imply
  IsInvertible I ↔ I * I⁻¹ = 1 :=
-- proof
  isInvertible_iff_mul_inv_eq_one I
end
section IdealGroupDef
variable (A : Type*) [CommRing A] [IsDomain A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]


/--
[mem_idealGroup_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma mem_idealGroup_iff
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {I : FractionalIdeal A⁰ K} :
-- imply
  IsUnit I ↔ FractionalIdeal.IsInvertible I :=
-- proof
  (FractionalIdeal.isInvertible_iff_isUnit I).symm
end IdealGroupDef
section IdealClassGroupDef
variable (A : Type*) [CommRing A] [IsDomain A]

/--
[IdealClassGroup.eq_classGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean)
-/
@[path]
lemma IdealClassGroup.eq_classGroup
  {A : Type*}
  [CommRing A]
  [IsDomain A] :
-- imply
  IdealClassGroup A = ClassGroup A :=
-- proof
  rfl
end IdealClassGroupDef


-- created on 2026-10-23
