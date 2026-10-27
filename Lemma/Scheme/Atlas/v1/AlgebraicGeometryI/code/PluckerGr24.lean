import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.PluckerGr24
open ExteriorAlgebra PluckerGr24
open scoped LinearAlgebra.Projectivization


namespace PluckerGr24

variable [CommRing R] [AddCommGroup M] [Module R M]
/--
[ι_anticomm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
lemma ι_anticomm (x y : M) :
  (ι R (M := M)) x * (ι R) y = -((ι R) y * (ι R (M := M)) x) := by
  have h := @ι_add_mul_swap R _ M _ _ y x
  rw [add_comm] at h
  exact eq_neg_of_add_eq_zero_left h

end PluckerGr24

namespace PluckerGr24

/--
[wedge_sq_zero_of_decomposable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
lemma wedge_sq_zero_of_decomposable
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  {v₁ v₂ : M} :
-- imply
  (ι R v₁ * ι R v₂) * (ι R v₁ * ι R v₂) = (0 : ExteriorAlgebra R M) := by
-- proof
  have anticomm : ι R v₂ * ι R v₁ = -((ι R (M := M)) v₁ * ι R v₂) := by
    have h := @ι_add_mul_swap R _ M _ _ v₁ v₂
    rw [add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [mul_assoc, ← mul_assoc (ι R v₂) (ι R v₁) (ι R v₂)]
  rw [anticomm]
  rw [neg_mul, mul_neg, mul_assoc, ← mul_assoc (ι R v₁) (ι R v₁)]
  rw [ι_sq_zero, zero_mul, neg_zero]

end PluckerGr24

namespace PluckerGr24

/--
[wedge_sq_zero_of_isDecomposable2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
lemma wedge_sq_zero_of_isDecomposable2
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  {ω : ExteriorAlgebra R M}
-- given
  (h : IsDecomposable2 ω) :
-- imply
  ω * ω = 0 := by
-- proof
  obtain ⟨v₁, v₂, rfl⟩ := h
  exact wedge_sq_zero_of_decomposable v₁ v₂

end PluckerGr24

namespace PluckerGr24

variable [CommRing R] [AddCommGroup M] [Module R M]
/--
[ι_pair_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
even-degree elements commute in the exterior algebra. -/
lemma ι_pair_comm (a b c d : M) :
  (ι R a * ι R b) * (ι R c * ι R d) = (ι R c * ι R d) * ((ι R (M := M)) a * ι R b) := by
  have hAC := ι_anticomm (R := R) a c
  have hBC := ι_anticomm (R := R) b c
  have hBD := ι_anticomm (R := R) b d
  have hAD := ι_anticomm (R := R) a d
  calc (ι R a * ι R b) * (ι R c * ι R d)
    = ι R a * (ι R b * ι R c) * ι R d := by rw [mul_assoc, mul_assoc, mul_assoc]
    _ = ι R a * (-(ι R c * ι R b)) * ι R d := by rw [hBC]
    _ = -(ι R a * (ι R c * ι R b) * ι R d) := by rw [mul_neg, neg_mul]
    _ = -((ι R a * ι R c) * ι R b * ι R d) := by rw [mul_assoc (ι R a) (ι R c)]
    _ = -((-(ι R c * ι R a)) * ι R b * ι R d) := by rw [hAC]
    _ = (ι R c * ι R a) * ι R b * ι R d := by simp [neg_mul, neg_neg]
    _ = ι R c * (ι R a * (ι R b * ι R d)) := by rw [mul_assoc, mul_assoc]
    _ = ι R c * (ι R a * (-(ι R d * ι R b))) := by rw [hBD]
    _ = -(ι R c * (ι R a * (ι R d * ι R b))) := by rw [mul_neg, mul_neg]
    _ = -(ι R c * ((ι R a * ι R d) * ι R b)) := by rw [mul_assoc (ι R a)]
    _ = -(ι R c * ((-(ι R d * ι R a)) * ι R b)) := by rw [hAD]
    _ = ι R c * (ι R d * ι R a * ι R b) := by simp [neg_mul, mul_neg, neg_neg]
    _ = ι R c * (ι R d * (ι R a * ι R b)) := by rw [mul_assoc (ι R d)]
    _ = ι R c * ι R d * (ι R a * ι R b) := by rw [mul_assoc]

end PluckerGr24

namespace PluckerGr24

/--
[wedge_sq_sum_decomposable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
lemma wedge_sq_sum_decomposable
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  {v₁ v₂ v₃ v₄ : M} :
-- imply
  (ι R v₁ * ι R v₂ + ι R v₃ * ι R v₄) * (ι R v₁ * ι R v₂ + ι R v₃ * ι R v₄) = 2 * ((ι R (M := M)) v₁ * ι R v₂ * (ι R v₃ * ι R v₄)) := by
-- proof
  rw [add_mul, mul_add, mul_add]
  rw [wedge_sq_zero_of_decomposable v₁ v₂, wedge_sq_zero_of_decomposable v₃ v₄]
  rw [zero_add, add_zero]
  rw [ι_pair_comm v₁ v₂ v₃ v₄]
  rw [two_mul]
section DimensionCount
variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
  [Module.Free k V] [Module.Finite k V]

end PluckerGr24

namespace PluckerGr24

/--
[exteriorPower_two_finrank_of_four](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
lemma exteriorPower_two_finrank_of_four
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
-- given
  (hdim : Module.finrank k V = 4) :
-- imply
  Module.finrank k (⋀[k]^2 V) = 6 := by
-- proof
  rw [exteriorPower.finrank_eq, hdim]
  decide

end PluckerGr24

namespace PluckerGr24

/--
[exteriorPower_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
lemma exteriorPower_finrank
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V] :
-- imply
  Module.finrank k (⋀[k]^(n : ℕ) V) = Nat.choose (Module.finrank k V) n := by
-- proof
  rw [exteriorPower.finrank_eq]

end PluckerGr24

namespace PluckerGr24

/--
[exteriorPower_four_finrank_of_four](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
lemma exteriorPower_four_finrank_of_four
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
-- given
  (hdim : Module.finrank k V = 4) :
-- imply
  Module.finrank k (⋀[k]^4 V) = 1 := by
-- proof
  rw [exteriorPower.finrank_eq, hdim]
  decide

end PluckerGr24

namespace PluckerGr24

/--
[decomposable_iff_wedge_sq_zero_forward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
lemma decomposable_iff_wedge_sq_zero_forward
  [Field k]
  {ω : ExteriorAlgebra k (Fin 4 → k)}
-- given
  (hω : IsDecomposable2 ω) :
-- imply
  ω * ω = 0 :=
-- proof
  wedge_sq_zero_of_isDecomposable2 hω
set_option maxHeartbeats 400000 in

end PluckerGr24

namespace PluckerGr24

variable [Field k]
/--
[ιMulti_stdBasis_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
of the 1-dimensional space ⋀⁴(k^4)). -/
lemma ιMulti_stdBasis_ne_zero :
  ExteriorAlgebra.ιMulti k 4 (Pi.basisFun k (Fin 4) : Fin 4 → Fin 4 → k) ≠ 0 := by
  intro h
  set b := Pi.basisFun k (Fin 4)
  set s : Set.powersetCard (Fin 4) 4 := ⟨Finset.univ, Finset.card_fin 4⟩
  have key : (exteriorPower.ιMulti_family k 4 (⇑b) s : ⋀[k]^4 (Fin 4 → k)) =
    exteriorPower.ιMulti k 4 (⇑b) := by
    simp only [exteriorPower.ιMulti_family, exteriorPower.ιMulti]
    congr 1
    funext i
    show b ((Set.powersetCard.ofFinEmbEquiv.symm s) i) = b i
    congr 1
    fin_cases i <;> native_decide
  have hdiag := exteriorPower.ιMultiDual_apply_diag k 4 b s
  rw [key] at hdiag
  have h_sub : exteriorPower.ιMulti k 4 (⇑b) = 0 := by
    apply Subtype.val_injective
    simp [exteriorPower.ιMulti_apply_coe, h]
  rw [h_sub, map_zero] at hdiag
  exact zero_ne_one hdiag

end PluckerGr24

namespace PluckerGr24

variable [Field k]
/--
[product_basis_eq_ιMulti](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
top wedge ιMulti(e_0, e_1, e_2, e_3). -/
lemma product_basis_eq_ιMulti :
  ι k (Pi.single 0 1 : Fin 4 → k) * ι k (Pi.single 1 1) *
    (ι k (Pi.single 2 1) * ι k (Pi.single 3 1)) =
  ExteriorAlgebra.ιMulti k 4 (Pi.basisFun k (Fin 4) : Fin 4 → Fin 4 → k) := by
  simp only [ιMulti_apply, List.ofFn_succ, Fin.isValue, List.prod_cons]
  simp [List.ofFn_zero]
  rw [mul_assoc]

end PluckerGr24

namespace PluckerGr24

/--
[non_decomposable_wedge_sq_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
lemma non_decomposable_wedge_sq_ne_zero
  [Field k]
  [CharZero k] :
-- imply
  (ι k (Pi.single 0 1 : Fin 4 → k) * ι k (Pi.single 1 1) + ι k (Pi.single 2 1 : Fin 4 → k) * ι k (Pi.single 3 1)) * (ι k (Pi.single 0 1 : Fin 4 → k) * ι k (Pi.single 1 1) + ι k (Pi.single 2 1 : Fin 4 → k) * ι k (Pi.single 3 1)) ≠ 0 := by
-- proof
  intro h
  rw [wedge_sq_sum_decomposable] at h
  rw [product_basis_eq_ιMulti] at h
  have hne : ExteriorAlgebra.ιMulti k 4 (Pi.basisFun k (Fin 4) : Fin 4 → Fin 4 → k) ≠ 0 :=
    ιMulti_stdBasis_ne_zero
  have hunit : IsUnit (2 : ExteriorAlgebra k (Fin 4 → k)) :=
    (IsUnit.mk0 (2 : k) two_ne_zero).map (algebraMap k _)
  exact hne (hunit.mul_left_cancel (by rw [mul_zero]; exact h))
section Converse
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
  [Module.Free k V] [Module.Finite k V]

end PluckerGr24

namespace PluckerGr24

/--
[isDecomposable2_of_wedge_sq_zero_dim_four](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
lemma isDecomposable2_of_wedge_sq_zero_dim_four
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [CharZero k]
  {ω : ExteriorAlgebra k V}
-- given
  (hdim : Module.finrank k V = 4)
  (hω2 : ω ∈ (⋀[k]^2 V : Submodule k (ExteriorAlgebra k V)))
  (hsq : ω * ω = 0) :
-- imply
  IsDecomposable2 ω :=
-- proof
  Lec4Grassmannian.alternating_form_classification_dim4 V hdim ω hω2 hsq

end PluckerGr24

namespace PluckerGr24

/--
[converse_wedge_sq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
lemma converse_wedge_sq_zero
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [CharZero k]
  {ω : ExteriorAlgebra k V}
-- given
  (hdim : Module.finrank k V = 4)
  (hω2 : ω ∈ (⋀[k]^2 V : Submodule k (ExteriorAlgebra k V)))
  (hsq : ω * ω = 0) :
-- imply
  IsDecomposable2 ω :=
-- proof
  isDecomposable2_of_wedge_sq_zero_dim_four hdim hω2 hsq

end PluckerGr24

namespace PluckerGr24

/--
[decomposable_iff_wedge_sq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
lemma decomposable_iff_wedge_sq_zero
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [CharZero k]
  {ω : ExteriorAlgebra k V}
-- given
  (hdim : Module.finrank k V = 4)
  (hω2 : ω ∈ (⋀[k]^2 V : Submodule k (ExteriorAlgebra k V))) :
-- imply
  IsDecomposable2 ω ↔ ω * ω = 0 :=
-- proof
  ⟨fun h => wedge_sq_zero_of_isDecomposable2 h,
    fun h => converse_wedge_sq_zero hdim hω2 h⟩
open scoped LinearAlgebra.Projectivization

end PluckerGr24

namespace PluckerGr24

/--
[gr24_lives_in_P5](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
lemma gr24_lives_in_P5
  {k : Type*}
  [Field k]
  [CharZero k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [Module.Free k V]
  [Module.Finite k V]
-- given
  (hdim : Module.finrank k V = 4) :
-- imply
  Module.finrank k (⋀[k]^2 V) = 6 ∧ Function.Injective (GrassmannianProjective.pluckerMap k V 2) ∧ Set.range (GrassmannianProjective.pluckerMap k V 2) = GrassmannianProjective.DecomposableProjective k V 2 ∧ (∀ (ω : ExteriorAlgebra k V), ω ∈ ⋀[k]^2 V → ω * ω = 0 → IsDecomposable2 ω) :=
-- proof
  ⟨exteriorPower_two_finrank_of_four k V hdim,
    GrassmannianProjective.plucker_embedding_injective k V 2,
    GrassmannianProjective.plucker_image_eq_decomposable k V 2,
    fun ω hω2 hωω =>
      Lec4Grassmannian.alternating_form_classification_dim4 V hdim ω hω2 hωω⟩

end PluckerGr24

/--
[product_basis_eq_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PluckerGr24.lean)
-/
@[path]
private lemma product_basis_eq__eq
  [Field k] :
-- imply
  ι k (Pi.single 0 1 : Fin 4 → k) * ι k (Pi.single 1 1) * (ι k (Pi.single 2 1) * ι k (Pi.single 3 1)) = ExteriorAlgebra.ιMulti k 4 (Pi.basisFun k (Fin 4) : Fin 4 → Fin 4 → k) := by
-- proof
  apply PluckerGr24.product_basis_eq_


-- created on 2026-10-23
