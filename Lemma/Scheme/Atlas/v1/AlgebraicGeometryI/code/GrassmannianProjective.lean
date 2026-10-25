import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.GrassmannianProjective.Part2
open ExteriorAlgebra GrassmannianProjective
open scoped LinearAlgebra.Projectivization


namespace GrassmannianProjective

/--
[plucker_ambient_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
lemma plucker_ambient_dim
  [Field K]
  {K : Type*}
  [Field K]
  {V : Type*}
  [AddCommGroup V]
  [Module K V]
  {k : ℕ} :
-- imply
  Module.finrank K (⋀[K]^k V) = Nat.choose (Module.finrank K V) k := by
-- proof
  rw [exteriorPower.finrank_eq]

end GrassmannianProjective

namespace GrassmannianProjective

/--
[plucker_target_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
lemma plucker_target_finrank
  [Field K]
  {K : Type*}
  [Field K]
  {V : Type*}
  [AddCommGroup V]
  [Module K V]
  {k n : ℕ}
-- given
  (hdim : Module.finrank K V = n) :
-- imply
  Module.finrank K (⋀[K]^k V) = Nat.choose n k := by
-- proof
  rw [exteriorPower.finrank_eq, hdim]

end GrassmannianProjective

namespace GrassmannianProjective

variable [Field K]
variable [CommRing K] [AddCommGroup M] [Module K M]
/--
[ι_anticomm_ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
lemma ι_anticomm_ext (x y : M) :
  (ι K (M := M)) x * (ι K) y = -((ι K) y * (ι K (M := M)) x) := by
  have h := @ι_add_mul_swap K _ M _ _ y x
  rw [add_comm] at h
  exact eq_neg_of_add_eq_zero_left h

end GrassmannianProjective

namespace GrassmannianProjective

/--
[wedge_sq_zero_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
lemma wedge_sq_zero_decomp
  [Field K]
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
  {v₁ v₂ : M} :
-- imply
  (ι K v₁ * ι K v₂) * (ι K v₁ * ι K v₂) = (0 : ExteriorAlgebra K M) := by
-- proof
  have anticomm : ι K v₂ * ι K v₁ = -((ι K (M := M)) v₁ * ι K v₂) := by
    have h := @ι_add_mul_swap K _ M _ _ v₁ v₂
    rw [add_comm] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [mul_assoc, ← mul_assoc (ι K v₂) (ι K v₁) (ι K v₂)]
  rw [anticomm]
  rw [neg_mul, mul_neg, mul_assoc, ← mul_assoc (ι K v₁) (ι K v₁)]
  rw [ι_sq_zero, zero_mul, neg_zero]

end GrassmannianProjective

namespace GrassmannianProjective

/--
[wedge_sq_zero_of_isDecomposableDeg2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
lemma wedge_sq_zero_of_isDecomposableDeg2
  [Field K]
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
  {ω : ExteriorAlgebra K M}
-- given
  (h : IsDecomposableDeg2 ω) :
-- imply
  ω * ω = 0 := by
-- proof
  obtain ⟨v₁, v₂, rfl⟩ := h
  exact wedge_sq_zero_decomp v₁ v₂

end GrassmannianProjective

namespace GrassmannianProjective

variable [Field K]
variable [CommRing K] [AddCommGroup M] [Module K M]
/--
[ι_pair_comm_deg2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
lemma ι_pair_comm_deg2 (a b c d : M) :
  (ι K a * ι K b) * (ι K c * ι K d) =
  (ι K c * ι K d) * ((ι K (M := M)) a * ι K b) := by
  have hAC := ι_anticomm_ext (K := K) a c
  have hBC := ι_anticomm_ext (K := K) b c
  have hBD := ι_anticomm_ext (K := K) b d
  have hAD := ι_anticomm_ext (K := K) a d
  calc (ι K a * ι K b) * (ι K c * ι K d)
    = ι K a * (ι K b * ι K c) * ι K d := by rw [mul_assoc, mul_assoc, mul_assoc]
    _ = ι K a * (-(ι K c * ι K b)) * ι K d := by rw [hBC]
    _ = -(ι K a * (ι K c * ι K b) * ι K d) := by rw [mul_neg, neg_mul]
    _ = -((ι K a * ι K c) * ι K b * ι K d) := by rw [mul_assoc (ι K a) (ι K c)]
    _ = -((-(ι K c * ι K a)) * ι K b * ι K d) := by rw [hAC]
    _ = (ι K c * ι K a) * ι K b * ι K d := by simp [neg_mul, neg_neg]
    _ = ι K c * (ι K a * (ι K b * ι K d)) := by rw [mul_assoc, mul_assoc]
    _ = ι K c * (ι K a * (-(ι K d * ι K b))) := by rw [hBD]
    _ = -(ι K c * (ι K a * (ι K d * ι K b))) := by rw [mul_neg, mul_neg]
    _ = -(ι K c * ((ι K a * ι K d) * ι K b)) := by rw [mul_assoc (ι K a)]
    _ = -(ι K c * ((-(ι K d * ι K a)) * ι K b)) := by rw [hAD]
    _ = ι K c * (ι K d * ι K a * ι K b) := by simp [neg_mul, mul_neg, neg_neg]
    _ = ι K c * (ι K d * (ι K a * ι K b)) := by rw [mul_assoc (ι K d)]
    _ = ι K c * ι K d * (ι K a * ι K b) := by rw [mul_assoc]

end GrassmannianProjective

namespace GrassmannianProjective

/--
[wedge_sq_sum_decomp_pair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
lemma wedge_sq_sum_decomp_pair
  [Field K]
  [CommRing K]
  [AddCommGroup M]
  [Module K M]
  {v₁ v₂ v₃ v₄ : M} :
-- imply
  (ι K v₁ * ι K v₂ + ι K v₃ * ι K v₄) * (ι K v₁ * ι K v₂ + ι K v₃ * ι K v₄) = 2 * ((ι K (M := M)) v₁ * ι K v₂ * (ι K v₃ * ι K v₄)) := by
-- proof
  rw [add_mul, mul_add, mul_add]
  rw [wedge_sq_zero_decomp v₁ v₂, wedge_sq_zero_decomp v₃ v₄]
  rw [zero_add, add_zero]
  rw [ι_pair_comm_deg2 v₁ v₂ v₃ v₄]
  rw [two_mul]

end GrassmannianProjective

namespace GrassmannianProjective

variable [Field K]
variable [Field K]
/--
[product_eq_ιMulti](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
of two wedges `v₁ ∧ v₂ + v₃ ∧ v₄` on a linearly independent basis. -/
lemma product_eq_ιMulti {V : Type*} [AddCommGroup V] [Module K V]
  (v₁ v₂ v₃ v₄ : V) :
  ι K v₁ * ι K v₂ * (ι K v₃ * ι K v₄) = ιMulti K 4 ![v₁, v₂, v₃, v₄] := by
  simp only [ιMulti_apply, List.ofFn_succ, Fin.isValue, List.prod_cons]
  simp [List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_assoc]
set_option maxHeartbeats 800000 in

end GrassmannianProjective

namespace GrassmannianProjective

variable [Field K]
variable [Field K]
/--
[ιMulti_ne_zero_of_linearIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
lemma ιMulti_ne_zero_of_linearIndependent
  {V : Type*} [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]
  (hdim : Module.finrank K V = 4) (v : Fin 4 → V)
  (hli : LinearIndependent K v) :
  ιMulti K 4 v ≠ 0 := by
  intro h
  have hcard : Fintype.card (Fin 4) = Module.finrank K V := by simp [hdim]
  set b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb_coe : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  set s : Set.powersetCard (Fin 4) 4 := ⟨Finset.univ, Finset.card_fin 4⟩
  have hdiag := exteriorPower.ιMultiDual_apply_diag K 4 b s
  have key : (exteriorPower.ιMulti_family K 4 (⇑b) s : ⋀[K]^4 V) =
    exteriorPower.ιMulti K 4 (⇑b) := by
    simp only [exteriorPower.ιMulti_family, exteriorPower.ιMulti]
    congr 1; funext i
    show b ((Set.powersetCard.ofFinEmbEquiv.symm s) i) = b i
    congr 1; exact orderEmb_fin_eq_id 4 (Set.powersetCard.ofFinEmbEquiv.symm s) i
  rw [key] at hdiag
  have h_sub : exteriorPower.ιMulti K 4 (⇑b) = 0 := by
    apply Subtype.val_injective
    simp only [hb_coe, exteriorPower.ιMulti_apply_coe, ZeroMemClass.coe_zero, h]
  rw [h_sub, map_zero] at hdiag
  exact zero_ne_one hdiag
variable [CharZero K]
/-- Lemma 6 converse for `dim V = 4` (char zero): if `ω ∈ ⋀^2 V` satisfies the Plücker relation
`ω ∧ ω = 0`, then `ω` is decomposable. -/
section Gr24
variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

end GrassmannianProjective

namespace GrassmannianProjective

/--
[gr24_plucker_target_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
lemma gr24_plucker_target_dim
  [Field K]
  {K : Type*}
  [Field K]
  {V : Type*}
  [AddCommGroup V]
  [Module K V]
-- given
  (hdim : Module.finrank K V = 4) :
-- imply
  Module.finrank K (⋀[K]^2 V) = 6 := by
-- proof
  rw [exteriorPower.finrank_eq, hdim]; decide

end GrassmannianProjective

namespace GrassmannianProjective

/--
[extPower_four_dim_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
lemma extPower_four_dim_one
  [Field K]
  {K : Type*}
  [Field K]
  {V : Type*}
  [AddCommGroup V]
  [Module K V]
-- given
  (hdim : Module.finrank K V = 4) :
-- imply
  Module.finrank K (⋀[K]^4 V) = 1 := by
-- proof
  rw [exteriorPower.finrank_eq, hdim]; decide
variable {K}
set_option maxHeartbeats 400000 in

end GrassmannianProjective

namespace GrassmannianProjective

variable [Field K]
variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V]
variable {K}
/--
[ιMulti_stdBasis_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
lemma ιMulti_stdBasis_nonzero :
  ExteriorAlgebra.ιMulti K 4 (Pi.basisFun K (Fin 4) : Fin 4 → Fin 4 → K) ≠ 0 := by
  intro h
  set b := Pi.basisFun K (Fin 4)
  set s : Set.powersetCard (Fin 4) 4 := ⟨Finset.univ, Finset.card_fin 4⟩
  have key : (exteriorPower.ιMulti_family K 4 (⇑b) s : ⋀[K]^4 (Fin 4 → K)) =
    exteriorPower.ιMulti K 4 (⇑b) := by
    simp only [exteriorPower.ιMulti_family, exteriorPower.ιMulti]
    congr 1; funext i
    show b ((Set.powersetCard.ofFinEmbEquiv.symm s) i) = b i
    congr 1; exact orderEmb_fin_eq_id 4 (Set.powersetCard.ofFinEmbEquiv.symm s) i
  have hdiag := exteriorPower.ιMultiDual_apply_diag K 4 b s
  rw [key] at hdiag
  have h_sub : exteriorPower.ιMulti K 4 (⇑b) = 0 := by
    apply Subtype.val_injective; simp [exteriorPower.ιMulti_apply_coe, h]
  rw [h_sub, map_zero] at hdiag
  exact zero_ne_one hdiag

end GrassmannianProjective

namespace GrassmannianProjective

variable [Field K]
variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V]
variable {K}
/--
[basis_product_is_ιMulti](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
lemma basis_product_is_ιMulti :
  ι K (Pi.single 0 1 : Fin 4 → K) * ι K (Pi.single 1 1) *
    (ι K (Pi.single 2 1) * ι K (Pi.single 3 1)) =
  ExteriorAlgebra.ιMulti K 4 (Pi.basisFun K (Fin 4) : Fin 4 → Fin 4 → K) := by
  simp only [ιMulti_apply, List.ofFn_succ, Fin.isValue, List.prod_cons]
  simp [List.ofFn_zero]
  rw [mul_assoc]

end GrassmannianProjective

namespace GrassmannianProjective

/--
[non_decomp_wedge_sq_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
lemma non_decomp_wedge_sq_ne_zero
  [Field K]
  {K : Type*}
  [Field K]
  {V : Type*}
  [AddCommGroup V]
  [Module K V]
  {K}
  [CharZero K] :
-- imply
  (ι K (Pi.single 0 1 : Fin 4 → K) * ι K (Pi.single 1 1) + ι K (Pi.single 2 1 : Fin 4 → K) * ι K (Pi.single 3 1)) * (ι K (Pi.single 0 1 : Fin 4 → K) * ι K (Pi.single 1 1) + ι K (Pi.single 2 1 : Fin 4 → K) * ι K (Pi.single 3 1)) ≠ 0 := by
-- proof
  intro h
  rw [wedge_sq_sum_decomp_pair] at h
  rw [basis_product_is_ιMulti] at h
  have hne : ExteriorAlgebra.ιMulti K 4 (Pi.basisFun K (Fin 4) : Fin 4 → Fin 4 → K) ≠ 0 :=
    ιMulti_stdBasis_nonzero
  have hunit : IsUnit (2 : ExteriorAlgebra K (Fin 4 → K)) :=
    (IsUnit.mk0 (2 : K) two_ne_zero).map (algebraMap K _)
  exact hne (hunit.mul_left_cancel (by rw [mul_zero]; exact h))
/-- Plücker embedding for `Gr(2, 4)`: ambient `P^5`, injective Plücker map, and `Gr(2, 4)` is
the quadric `{ω : ω ∧ ω = 0}` in `P(⋀^2 V)` (char zero, `dim V = 4`). -/

end GrassmannianProjective

/--
[orderEmb_fin_eq_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
private lemma orderEmb_fin_eq_id_eq
  {n : ℕ}
  {f : Fin n ↪o Fin n}
  {i : Fin n} :
-- imply
  f i = i := by
-- proof
  apply GrassmannianProjective.orderEmb_fin_eq_id n f i

/--
[plucker_coord_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
private lemma plucker_coord_ne_zero_eq
  [Field K]
  {K : Type*}
  [Field K]
  {V : Type*}
  [AddCommGroup V]
  [Module K V]
  {k : ℕ}
  {W : Submodule K V}
-- given
  (hk : Module.finrank K W = k) :
-- imply
  pluckerCoord K V k W hk ≠ 0 := by
-- proof
  apply GrassmannianProjective.plucker_coord_ne_zero K V k W hk

/--
[product_eq_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
private lemma product_eq__eq
  [Field K]
  [Field K]
  [AddCommGroup V]
  [Module K V]
  {v₁ v₂ v₃ v₄ : V} :
-- imply
  ι K v₁ * ι K v₂ * (ι K v₃ * ι K v₄) = ιMulti K 4 ![v₁, v₂, v₃, v₄] := by
-- proof
  apply GrassmannianProjective.product_eq_ v₁ v₂ v₃ v₄

/--
[basis_product_is_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianProjective.lean)
-/
@[path]
private lemma basis_product_is__eq
  [Field K]
  {K : Type*}
  [Field K]
  {V : Type*}
  [AddCommGroup V]
  [Module K V]
  {K} :
-- imply
  ι K (Pi.single 0 1 : Fin 4 → K) * ι K (Pi.single 1 1) * (ι K (Pi.single 2 1) * ι K (Pi.single 3 1)) = ExteriorAlgebra.ιMulti K 4 (Pi.basisFun K (Fin 4) : Fin 4 → Fin 4 → K) := by
-- proof
  apply GrassmannianProjective.basis_product_is_ K V


-- created on 2026-10-23
