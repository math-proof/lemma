import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec4Grassmannian
open ExteriorAlgebra Lec4Grassmannian


namespace Lec4Grassmannian

/--
[plucker_ambient_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Grassmannian.lean)
-/
@[path]
lemma plucker_ambient_finrank
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

end Lec4Grassmannian

namespace Lec4Grassmannian

variable [CommRing R] [AddCommGroup M] [Module R M]
/--
[ι_anticommute](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Grassmannian.lean)
-/
@[path]
lemma ι_anticommute (x y : M) :
  (ι R (M := M)) x * (ι R) y = -((ι R) y * (ι R (M := M)) x) := by
  have h := @ι_add_mul_swap R _ M _ _ y x
  rw [add_comm] at h
  exact eq_neg_of_add_eq_zero_left h

end Lec4Grassmannian

namespace Lec4Grassmannian

/--
[wedge_sq_zero_of_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Grassmannian.lean)
-/
@[path]
lemma wedge_sq_zero_of_decomp
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

end Lec4Grassmannian

namespace Lec4Grassmannian

/--
[lemma6_forward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Grassmannian.lean)
-/
@[path]
lemma lemma6_forward
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  {ω : ExteriorAlgebra R M}
-- given
  (h : IsDecomposableTwo ω) :
-- imply
  ω * ω = 0 := by
-- proof
  obtain ⟨v₁, v₂, rfl⟩ := h
  exact wedge_sq_zero_of_decomp v₁ v₂

end Lec4Grassmannian

namespace Lec4Grassmannian

variable [Field K]
/--
[ι_pair_commute](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Grassmannian.lean)
-/
@[path]
lemma ι_pair_commute {M : Type*} [AddCommGroup M] [Module K M] (a b c d : M) :
  (ι K a * ι K b) * (ι K c * ι K d) =
  (ι K c * ι K d) * ((ι K (M := M)) a * ι K b) := by
  have hAC := ι_anticommute (R := K) a c
  have hBC := ι_anticommute (R := K) b c
  have hBD := ι_anticommute (R := K) b d
  have hAD := ι_anticommute (R := K) a d
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

end Lec4Grassmannian

namespace Lec4Grassmannian

/--
[wedge_sq_sum_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Grassmannian.lean)
-/
@[path]
lemma wedge_sq_sum_decomp
  [Field K]
  [AddCommGroup M]
  [Module K M]
  {v₁ v₂ v₃ v₄ : M} :
-- imply
  (ι K v₁ * ι K v₂ + ι K v₃ * ι K v₄) * (ι K v₁ * ι K v₂ + ι K v₃ * ι K v₄) = 2 * ((ι K (M := M)) v₁ * ι K v₂ * (ι K v₃ * ι K v₄)) := by
-- proof
  rw [add_mul, mul_add, mul_add]
  rw [wedge_sq_zero_of_decomp v₁ v₂,
    wedge_sq_zero_of_decomp v₃ v₄]
  rw [zero_add, add_zero]
  rw [ι_pair_commute v₁ v₂ v₃ v₄]
  rw [two_mul]

end Lec4Grassmannian

namespace Lec4Grassmannian

/--
[extPower_two_finrank_of_four](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Grassmannian.lean)
-/
@[path]
lemma extPower_two_finrank_of_four
  [Field K]
  {V : Type*}
  [AddCommGroup V]
  [Module K V]
  [Module.Free K V]
  [Module.Finite K V]
-- given
  (hdim : Module.finrank K V = 4) :
-- imply
  Module.finrank K (⋀[K]^2 V) = 6 := by
-- proof
  rw [exteriorPower.finrank_eq, hdim]
  decide

end Lec4Grassmannian

namespace Lec4Grassmannian

/--
[extPower_four_finrank_of_four](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Grassmannian.lean)
-/
@[path]
lemma extPower_four_finrank_of_four
  [Field K]
  {V : Type*}
  [AddCommGroup V]
  [Module K V]
  [Module.Free K V]
  [Module.Finite K V]
-- given
  (hdim : Module.finrank K V = 4) :
-- imply
  Module.finrank K (⋀[K]^4 V) = 1 := by
-- proof
  rw [exteriorPower.finrank_eq, hdim]
  decide

end Lec4Grassmannian

namespace Lec4Grassmannian

/--
[orderEmb_fin_eq_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Grassmannian.lean)
-/
@[path]
lemma orderEmb_fin_eq_id
  [Field K]
  {n : ℕ}
  {f : Fin n ↪o Fin n}
  {i : Fin n} :
-- imply
  f i = i := by
-- proof
  have hf := f.strictMono
  have h_surj : Function.Surjective f := Finite.surjective_of_injective f.injective
  have h_ge : ∀ j : Fin n, (j : ℕ) ≤ (f j : ℕ) := by
    intro ⟨j, hj⟩
    induction j with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hk : k < n := Nat.lt_of_succ_lt hj
      have hih := ih hk
      have hlt : (f ⟨k, hk⟩ : ℕ) < (f ⟨k + 1, hj⟩ : ℕ) :=
        hf (show (⟨k, hk⟩ : Fin n) < ⟨k + 1, hj⟩ by simp [Fin.lt_def])
      simp only at hih hlt ⊢; omega
  have h_le : ∀ j : Fin n, (f j : ℕ) ≤ (j : ℕ) := by
    by_contra h; push Not at h; obtain ⟨j, hj⟩ := h
    set e := Equiv.ofBijective f ⟨f.injective, h_surj⟩
    have hsum : ∑ i : Fin n, (f i : ℕ) = ∑ i : Fin n, (i : ℕ) := by
      conv_rhs => rw [show (fun i : Fin n => (i : ℕ)) =
        (fun i => (e (e.symm i) : ℕ)) from by ext; simp]
      rw [← Equiv.sum_comp e.symm]; simp [e, Equiv.ofBijective]
    exact absurd hsum (Nat.ne_of_gt
      (Finset.sum_lt_sum (fun i _ => h_ge i) ⟨j, Finset.mem_univ j, by omega⟩))
  exact Fin.ext (Nat.le_antisymm (h_le i) (h_ge i))

end Lec4Grassmannian

namespace Lec4Grassmannian

variable [Field K]
/--
[product_eq_ιMulti](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Grassmannian.lean)
-/
@[path]
`ιMulti K 4` applied to the 4-tuple. -/
lemma product_eq_ιMulti {V : Type*} [AddCommGroup V] [Module K V]
  (v₁ v₂ v₃ v₄ : V) :
  ι K v₁ * ι K v₂ * (ι K v₃ * ι K v₄) = ιMulti K 4 ![v₁, v₂, v₃, v₄] := by
  simp only [ιMulti_apply, List.ofFn_succ, Fin.isValue, List.prod_cons]
  simp [List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_assoc]
set_option maxHeartbeats 800000 in

end Lec4Grassmannian

namespace Lec4Grassmannian

variable [Field K]
/--
[ιMulti_ne_zero_of_linearIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Grassmannian.lean)
-/
@[path]
lemma ιMulti_ne_zero_of_linearIndependent
  {V : Type*} [AddCommGroup V] [Module K V]
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
    congr 1
    funext i
    show b ((Set.powersetCard.ofFinEmbEquiv.symm s) i) = b i
    congr 1
    exact orderEmb_fin_eq_id 4 (Set.powersetCard.ofFinEmbEquiv.symm s) i
  rw [key] at hdiag
  have h_sub : exteriorPower.ιMulti K 4 (⇑b) = 0 := by
    apply Subtype.val_injective
    simp only [hb_coe, exteriorPower.ιMulti_apply_coe, ZeroMemClass.coe_zero, h]
  rw [h_sub, map_zero] at hdiag
  exact zero_ne_one hdiag
variable [CharZero K]
/-- In dimension 4, a 2-form with zero wedge square must be decomposable: this is the converse
half of the classification used in Lemma 6. -/
section Gr24
variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

end Lec4Grassmannian

namespace Lec4Grassmannian

/--
[gr24_ambient_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Grassmannian.lean)
-/
@[path]
lemma gr24_ambient_dim
  {K : Type*}
  [Field K]
  {V : Type*}
  [AddCommGroup V]
  [Module K V]
-- given
  (hdim : Module.finrank K V = 4) :
-- imply
  Module.finrank K (⋀[K]^2 V) = 6 :=
-- proof
  extPower_two_finrank_of_four V hdim

end Lec4Grassmannian

/--
[product_eq_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Grassmannian.lean)
-/
@[path]
private lemma product_eq__eq
  [Field K]
  [AddCommGroup V]
  [Module K V]
  {v₁ v₂ v₃ v₄ : V} :
-- imply
  ι K v₁ * ι K v₂ * (ι K v₃ * ι K v₄) = ιMulti K 4 ![v₁, v₂, v₃, v₄] := by
-- proof
  apply Lec4Grassmannian.product_eq_ v₁ v₂ v₃ v₄


-- created on 2026-10-23
