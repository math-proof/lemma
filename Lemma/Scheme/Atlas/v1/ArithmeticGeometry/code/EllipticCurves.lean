import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.EllipticCurves
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open Polynomial Matrix GeneralLinearGroup OnePoint
open WeierstrassCurve.Affine
open ArithmeticGeometry


/--
[exists_variableChange_a₁_a₂_a₃_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma WeierstrassCurve.exists_variableChange_a₁_a₂_a₃_eq_zero
  {k : Type*} [Field k] (hchar2 : (2 : k) ≠ 0) (hchar3 : (3 : k) ≠ 0)
  (W : WeierstrassCurve k) :
  ∃ C : VariableChange k, (C • W).a₁ = 0 ∧ (C • W).a₂ = 0 ∧ (C • W).a₃ = 0 := by
  set C₁ : VariableChange k := ⟨1, 0, -(W.a₁ / 2), -(W.a₃ / 2)⟩
  set W₁ := C₁ • W
  have hW₁_a₁ : W₁.a₁ = 0 := by
    simp [W₁, variableChange_a₁, C₁]
    field_simp
    ring
  have hW₁_a₃ : W₁.a₃ = 0 := by
    simp [W₁, variableChange_a₃, C₁]
    field_simp
    ring
  set C₂ : VariableChange k := ⟨1, -(W₁.a₂ / 3), 0, 0⟩
  refine ⟨C₂ * C₁, ?_, ?_, ?_⟩
  ·
    rw [mul_smul, show C₁ • W = W₁ from rfl, variableChange_a₁]
    simp [C₂, hW₁_a₁]
  ·
    rw [mul_smul, show C₁ • W = W₁ from rfl, variableChange_a₂]
    simp [C₂, hW₁_a₁]
    field_simp
    ring
  ·
    rw [mul_smul, show C₁ • W = W₁ from rfl, variableChange_a₃]
    simp [C₂, hW₁_a₁, hW₁_a₃]

namespace WeierstrassCurve

/--
[isElliptic_shortNF_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma isElliptic_shortNF_iff
  [CommRing R]
  {A B : R}
  [Field F]
  [NeZero (2 : F)]
  {W : WeierstrassCurve F}
  [W.IsShortNF] :
-- imply
  W.IsElliptic ↔ 4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2 ≠ 0 := by
-- proof
  rw [isElliptic_iff, Δ_of_isShortNF, isUnit_iff_ne_zero, mul_ne_zero_iff]
  constructor
  · exact fun ⟨_, h⟩ => h
  · intro h
    exact ⟨by rw [neg_ne_zero]; exact_mod_cast pow_ne_zero 4 (NeZero.ne (2 : F)), h⟩

end WeierstrassCurve

namespace WeierstrassCurve

/--
[shortWeierstrass_isElliptic_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma shortWeierstrass_isElliptic_iff
  [CommRing R]
  {A B : R}
  [Field F]
  [NeZero (2 : F)]
  {A B : F} :
-- imply
  (shortWeierstrass A B).IsElliptic ↔ 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 :=
-- proof
  isElliptic_shortNF_iff (shortWeierstrass A B)

end WeierstrassCurve

namespace WeierstrassCurve.Affine.Point

/--
[divisorClassMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma divisorClassMap_injective
  [Field F]
  {W : WeierstrassCurve.Affine F}
  [DecidableEq F] :
-- imply
  Function.Injective (toClass : W.Point → Additive (ClassGroup W.CoordinateRing)) :=
-- proof
  toClass_injective
end WeierstrassCurve.Affine.Point
section Lemma_23_7
open Polynomial Matrix GeneralLinearGroup OnePoint


/--
[aut_P1_fixing_three_points_is_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma aut_P1_fixing_three_points_is_identity
  [Field K]
  [DecidableEq K]
  {g : GL (Fin 2) K}
  {p₁ p₂ p₃ : OnePoint K}
-- given
  (h₁₂ : p₁ ≠ p₂)
  (h₁₃ : p₁ ≠ p₃)
  (h₂₃ : p₂ ≠ p₃)
  (hf₁ : g • p₁ = p₁)
  (hf₂ : g • p₂ = p₂)
  (hf₃ : g • p₃ = p₃) :
-- imply
  ∀ p : OnePoint K, g • p = p := by
-- proof
  have hfp : g.fixpointPolynomial = 0 := by
    have eval_root : ∀ c : K, g • (c : OnePoint K) = c → g.fixpointPolynomial.eval c = 0 := by
      intro c hc
      have := fixpointPolynomial_aeval_eq_zero_iff.mpr hc
      simpa [aeval_def, eval₂_eq_eval_map] using this
    cases p₁ with
    | coe c₁ => cases p₂ with
      | coe c₂ => cases p₃ with
        | coe c₃ =>
          apply eq_zero_of_degree_lt_of_eval_finset_eq_zero (s := {c₁, c₂, c₃})
          · rw [show ({c₁, c₂, c₃} : Finset K).card = 3 from by
            simp [Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton,
              show c₁ ≠ c₂ from fun h => h₁₂ (congrArg _ h),
              show c₁ ≠ c₃ from fun h => h₁₃ (congrArg _ h),
              show c₂ ≠ c₃ from fun h => h₂₃ (congrArg _ h)]]
            calc g.fixpointPolynomial.degree ≤ 2 := by
              apply degree_le_of_natDegree_le; unfold fixpointPolynomial
              rw [sub_eq_add_neg, ← C_neg]; exact natDegree_quadratic_le
              _ < 3 := by norm_num
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            obtain rfl | rfl | rfl <;> exact eval_root _ (by assumption) := hx
        | infty =>
          have h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := smul_infty_eq_self_iff.mp hf₃
          apply eq_zero_of_degree_lt_of_eval_finset_eq_zero (s := {c₁, c₂})
          · rw [Finset.card_pair (fun h => h₁₂ (congrArg _ h))]
            calc g.fixpointPolynomial.degree ≤ 1 := by
              apply degree_le_of_natDegree_le; unfold fixpointPolynomial
              rw [h10, sub_eq_add_neg, ← C_neg]
              simp only [map_zero, zero_mul, zero_add]; exact natDegree_linear_le
              _ < 2 := by norm_num
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            obtain rfl | rfl <;> exact eval_root _ (by assumption) := hx
      | infty => cases p₃ with
        | coe c₃ =>
          have h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := smul_infty_eq_self_iff.mp hf₂
          apply eq_zero_of_degree_lt_of_eval_finset_eq_zero (s := {c₁, c₃})
          · rw [Finset.card_pair (fun h => h₁₃ (congrArg _ h))]
            calc g.fixpointPolynomial.degree ≤ 1 := by
              apply degree_le_of_natDegree_le; unfold fixpointPolynomial
              rw [h10, sub_eq_add_neg, ← C_neg]
              simp only [map_zero, zero_mul, zero_add]; exact natDegree_linear_le
              _ < 2 := by norm_num
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            obtain rfl | rfl <;> exact eval_root _ (by assumption) := hx
        | infty => exact absurd rfl h₂₃
    | infty => cases p₂ with
      | coe c₂ => cases p₃ with
        | coe c₃ =>
          have h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := smul_infty_eq_self_iff.mp hf₁
          apply eq_zero_of_degree_lt_of_eval_finset_eq_zero (s := {c₂, c₃})
          · rw [Finset.card_pair (fun h => h₂₃ (congrArg _ h))]
            calc g.fixpointPolynomial.degree ≤ 1 := by
              apply degree_le_of_natDegree_le; unfold fixpointPolynomial
              rw [h10, sub_eq_add_neg, ← C_neg]
              simp only [map_zero, zero_mul, zero_add]; exact natDegree_linear_le
              _ < 2 := by norm_num
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            obtain rfl | rfl <;> exact eval_root _ (by assumption) := hx
        | infty => exact absurd rfl h₁₃
      | infty => exact absurd rfl h₁₂
  have hscalar := fixpointPolynomial_eq_zero_iff.mp hfp
  obtain ⟨a, ha⟩ := hscalar
  intro p
  cases p with
  | infty => rw [smul_infty_eq_self_iff]; simp [← ha]
  | coe c =>
    rw [smul_some_eq_ite]
    have h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by simp [← ha]
    have h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = a := by simp [← ha]
    have h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = a := by simp [← ha]
    have h01 : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by simp [← ha]
    have ha_ne : a ≠ 0 := by
      intro ha0
      exact g.det_ne_zero (by rw [← ha, det_fin_two]; simp [ha0])
    simp [h10, h11, h00, h01, ha_ne]
end Lemma_23_7

namespace WeierstrassCurve.Affine.Point

/--
[geometric_group_law](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma geometric_group_law
  [Field F]
  {W : WeierstrassCurve.Affine F}
  [DecidableEq F]
  {P Q : W.Point} :
-- imply
  P + Q = -(lineThirdIntersection P Q) := by
-- proof
  cases P with
  | zero =>
    simp only [lineThirdIntersection, ← zero_def, zero_add, neg_neg]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      simp only [lineThirdIntersection, ← zero_def, add_zero, neg_neg]
    | some x₂ y₂ h₂ =>
      simp only [lineThirdIntersection]
      split_ifs with hxy
      · rw [neg_zero]
        exact add_of_Y_eq hxy.1 hxy.2
      · rw [add_some hxy, neg_some]
        simp only [addY]
end WeierstrassCurve.Affine.Point
section NTorsion


/--
[mem_nTorsionSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma mem_nTorsionSubgroup
  [AddCommGroup G]
  {n : ℕ}
  {P : G} :
-- imply
  P ∈ nTorsionSubgroup n ↔ n • P = 0 := by
-- proof
  simp [nTorsionSubgroup]
end NTorsion
namespace WeierstrassCurve.Affine.Point
variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}

namespace WeierstrassCurve

/--
[VariableChange.u_inv_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma VariableChange.u_inv_ne_zero
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  {C : VariableChange F} :
-- imply
  (↑C.u⁻¹ : F) ≠ 0 := by
-- proof
  simp only [Units.val_inv_eq_inv_val, ne_eq, inv_eq_zero]; exact Units.ne_zero C.u

end WeierstrassCurve

namespace WeierstrassCurve

variable [Field F] {W : WeierstrassCurve F} [W.IsShortNF]
/--
[aut_u_inv_pow4_mul_a₄](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma aut_u_inv_pow4_mul_a₄ {C : VariableChange F} (hC : C • W = W)
  (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
  (↑C.u⁻¹ : F) ^ 4 * W.a₄ = W.a₄ := by
  have ha4 : (C • W).a₄ = W.a₄ := by rw [hC]
  rw [variableChange_a₄] at ha4
  simp only [IsShortNF.a₁ (W := W), IsShortNF.a₂ (W := W), IsShortNF.a₃ (W := W),
    aut_s_eq_zero hC h2, aut_r_eq_zero hC h2 h3, aut_t_eq_zero hC h2 h3] at ha4
  ring_nf at ha4 ⊢; exact ha4

end WeierstrassCurve

namespace WeierstrassCurve

variable [Field F] {W : WeierstrassCurve F} [W.IsShortNF]
/--
[aut_u_inv_pow6_mul_a₆](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma aut_u_inv_pow6_mul_a₆ {C : VariableChange F} (hC : C • W = W)
  (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
  (↑C.u⁻¹ : F) ^ 6 * W.a₆ = W.a₆ := by
  have ha6 : (C • W).a₆ = W.a₆ := by rw [hC]
  rw [variableChange_a₆] at ha6
  simp only [IsShortNF.a₁ (W := W), IsShortNF.a₂ (W := W), IsShortNF.a₃ (W := W),
    aut_r_eq_zero hC h2 h3, aut_t_eq_zero hC h2 h3] at ha6
  ring_nf at ha6 ⊢; exact ha6

end WeierstrassCurve

namespace WeierstrassCurve

/--
[aut_u_inv_pow2_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma aut_u_inv_pow2_eq_one
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  {C : VariableChange F}
-- given
  (hC : C • W = W)
  (h2 : (2 : F) ≠ 0)
  (h3 : (3 : F) ≠ 0)
  (ha4 : W.a₄ ≠ 0)
  (ha6 : W.a₆ ≠ 0) :
-- imply
  (↑C.u⁻¹ : F) ^ 2 = 1 := by
-- proof
  have h4 := aut_u_inv_pow4_eq_one hC h2 h3 ha4
  have h6 := aut_u_inv_pow6_eq_one hC h2 h3 ha6
  have : (↑C.u⁻¹ : F) ^ 6 = (↑C.u⁻¹ : F) ^ 4 * (↑C.u⁻¹ : F) ^ 2 := by ring
  rw [h6, h4, one_mul] at this; exact this.symm

end WeierstrassCurve

namespace WeierstrassCurve

variable [Field F] {W : WeierstrassCurve F} [W.IsShortNF]
/--
[a₄_ne_zero_or_a₆_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma a₄_ne_zero_or_a₆_ne_zero [W.IsElliptic] : W.a₄ ≠ 0 ∨ W.a₆ ≠ 0 := by
  by_contra h
  push Not at h
  exact W.isUnit_Δ.ne_zero (by
    simp only [Δ, b₂, b₄, b₆, b₈,
      IsShortNF.a₁ (W := W), IsShortNF.a₂ (W := W), IsShortNF.a₃ (W := W), h.1, h.2]; ring)

end WeierstrassCurve

namespace WeierstrassCurve

/--
[autGroupToFHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma autGroupToFHom_injective
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  [W.IsElliptic]
-- given
  (h2 : (2 : F) ≠ 0)
  (h3 : (3 : F) ≠ 0) :
-- imply
  Function.Injective (autGroupToFHom h2 h3 : autGroup F W →* F) := by
-- proof
  intro ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ h
  simp only [autGroupToFHom, MonoidHom.coe_mk, OneHom.coe_mk] at h
  have hu : C₁.u = C₂.u := Units.val_injective h
  exact Subtype.ext (VariableChange.ext hu
    (by rw [aut_r_eq_zero hC₁ h2 h3, aut_r_eq_zero hC₂ h2 h3])
    (by rw [aut_s_eq_zero hC₁ h2, aut_s_eq_zero hC₂ h2])
    (by rw [aut_t_eq_zero hC₁ h2 h3, aut_t_eq_zero hC₂ h2 h3]))

end WeierstrassCurve

namespace WeierstrassCurve

/--
[autGroup_isCyclic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma autGroup_isCyclic
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  [W.IsElliptic]
-- given
  (h2 : (2 : F) ≠ 0)
  (h3 : (3 : F) ≠ 0) :
-- imply
  IsCyclic (autGroup F W) := by
-- proof
  haveI : Finite (autGroup F W) := autGroup_finite h2 h3
  exact isCyclic_of_injective_ringHom (autGroupToFHom h2 h3) (autGroupToFHom_injective h2 h3)

end WeierstrassCurve

namespace WeierstrassCurve

/--
[autGroup_u_sq_eq_one_of_generic_j](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma autGroup_u_sq_eq_one_of_generic_j
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  [W.IsElliptic]
  {C : VariableChange F}
-- given
  (h2 : (2 : F) ≠ 0)
  (h3 : (3 : F) ≠ 0)
  (ha4 : W.a₄ ≠ 0)
  (ha6 : W.a₆ ≠ 0)
  (hC : C ∈ autGroup F W) :
-- imply
  C.u ^ 2 = 1 ∧ C.r = 0 ∧ C.s = 0 ∧ C.t = 0 :=
-- proof
  ⟨u_pow_eq_one_of_inv_val_pow_eq_one (aut_u_inv_pow2_eq_one hC h2 h3 ha4 ha6),
    aut_r_eq_zero hC h2 h3, aut_s_eq_zero hC h2, aut_t_eq_zero hC h2 h3⟩

end WeierstrassCurve

namespace WeierstrassCurve

/--
[neg_one_mem_autGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma neg_one_mem_autGroup
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  [W.IsElliptic] :
-- imply
  (⟨-1, 0, 0, 0⟩ : VariableChange F) ∈ autGroup F W := by
-- proof
  show (⟨-1, 0, 0, 0⟩ : VariableChange F) • W = W
  rw [variableChange_def]
  ext <;> simp [Units.val_neg, Units.val_one] <;> ring

end WeierstrassCurve

namespace WeierstrassCurve

/--
[neg_one_ne_one_variableChange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma neg_one_ne_one_variableChange
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  [W.IsElliptic]
-- given
  (h2 : (2 : F) ≠ 0) :
-- imply
  (⟨-1, 0, 0, 0⟩ : VariableChange F) ≠ 1 := by
-- proof
  rw [VariableChange.one_def]
  intro h
  have := congr_arg VariableChange.u h
  simp only at this
  have hF : (-1 : F) = 1 := by
    have := congr_arg Units.val this; simpa using this
  apply h2
  have h' : (1 : F) + 1 = 0 := by
    have h0 : (-1 : F) + 1 = 0 := by ring
    rwa [hF] at h0
  have h1 : (2 : F) = 1 + 1 := by norm_num
  rw [h1]; exact h'

end WeierstrassCurve

namespace WeierstrassCurve

/--
[vc_eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma vc_eq_one_or_neg_one
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  [W.IsElliptic]
  {C : VariableChange F}
-- given
  (hu : C.u ^ 2 = 1)
  (hr : C.r = 0)
  (hs : C.s = 0)
  (ht : C.t = 0) :
-- imply
  C = 1 ∨ C = ⟨-1, 0, 0, 0⟩ := by
-- proof
  have hv : (↑C.u : F) ^ 2 = 1 := by
    have := congr_arg Units.val hu
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this; exact this
  obtain h1 | h1 := sq_eq_one_iff.mp hv
  · left; rw [VariableChange.one_def]
    exact VariableChange.ext (Units.val_injective (by simpa using h1)) hr hs ht
  · right
    exact VariableChange.ext (Units.val_injective (by simpa using h1)) hr hs ht

end WeierstrassCurve

namespace WeierstrassCurve

/--
[autGroup_card_eq_two_of_generic_j](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma autGroup_card_eq_two_of_generic_j
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  [W.IsElliptic]
-- given
  (h2 : (2 : F) ≠ 0)
  (h3 : (3 : F) ≠ 0)
  (ha4 : W.a₄ ≠ 0)
  (ha6 : W.a₆ ≠ 0) :
-- imply
  Nat.card (autGroup F W) = 2 := by
-- proof
  haveI : Finite (autGroup F W) := by
    haveI : Finite (rootsOfUnity 12 F) := Finite.of_fintype _
    let f : autGroup F W → rootsOfUnity 12 F := fun C =>
      ⟨(C : VariableChange F).u,
        (mem_rootsOfUnity 12 _).mpr (by
          have h4 := u_pow_eq_one_of_inv_val_pow_eq_one (aut_u_inv_pow4_eq_one C.2 h2 h3 ha4)
          have : C.val.u ^ 12 = (C.val.u ^ 4) ^ 3 := by group
          rw [this, h4, one_pow])  ⟩
    apply Finite.of_injective f
    intro ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ h
    have hu : C₁.u = C₂.u := congr_arg Subtype.val h
    exact Subtype.ext (VariableChange.ext hu
      (by rw [aut_r_eq_zero hC₁ h2 h3, aut_r_eq_zero hC₂ h2 h3])
      (by rw [aut_s_eq_zero hC₁ h2, aut_s_eq_zero hC₂ h2])
      (by rw [aut_t_eq_zero hC₁ h2 h3, aut_t_eq_zero hC₂ h2 h3]))
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, Subgroup.one_mem _⟩, ⟨⟨-1, 0, 0, 0⟩, neg_one_mem_autGroup⟩, ?_, ?_⟩
  · intro h
    exact neg_one_ne_one_variableChange h2
      (congr_arg Subtype.val h).symm
  · apply Set.eq_univ_of_forall
    intro ⟨C, hC⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have := autGroup_u_sq_eq_one_of_generic_j h2 h3 ha4 ha6 hC
    obtain h | h := vc_eq_one_or_neg_one this.1 this.2.1 this.2.2.1 this.2.2.2
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

end WeierstrassCurve

namespace WeierstrassCurve

/--
[autGroup_card_eq_four_of_j_1728](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma autGroup_card_eq_four_of_j_1728
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  [W.IsElliptic]
  {ζ : F}
-- given
  (h2 : (2 : F) ≠ 0)
  (h3 : (3 : F) ≠ 0)
  (ha4 : W.a₄ ≠ 0)
  (ha6 : W.a₆ = 0)
  (hζ : IsPrimitiveRoot ζ 4) :
-- imply
  Nat.card (autGroup F W) = 4 := by
-- proof
  haveI : NeZero (4 : ℕ) := ⟨by omega⟩
  have hcard := hζ.card_rootsOfUnity
  rw [show Nat.card (autGroup F W) =
    Nat.card (rootsOfUnity 4 F) from
    Nat.card_congr (autGroupEquivRootsOfUnity4 h2 h3 ha4 ha6)]
  rw [Nat.card_eq_fintype_card, hcard]

end WeierstrassCurve

namespace WeierstrassCurve

/--
[autGroup_card_eq_six_of_j_0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma autGroup_card_eq_six_of_j_0
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  [W.IsElliptic]
  {ζ : F}
-- given
  (h2 : (2 : F) ≠ 0)
  (h3 : (3 : F) ≠ 0)
  (ha6 : W.a₆ ≠ 0)
  (ha4 : W.a₄ = 0)
  (hζ : IsPrimitiveRoot ζ 6) :
-- imply
  Nat.card (autGroup F W) = 6 := by
-- proof
  haveI : NeZero (6 : ℕ) := ⟨by omega⟩
  have hcard := hζ.card_rootsOfUnity
  rw [show Nat.card (autGroup F W) =
    Nat.card (rootsOfUnity 6 F) from
    Nat.card_congr (autGroupEquivRootsOfUnity6 h2 h3 ha6 ha4)]
  rw [Nat.card_eq_fintype_card, hcard]
end WeierstrassCurve
section Theorem_23_20


namespace WeierstrassCurve.Affine

/--
[shortNF_addX](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma shortNF_addX
  [Field F]
  {W' : WeierstrassCurve F}
  [W'.IsShortNF]
  {x₁ x₂ ℓ : F} :
-- imply
  W'.toAffine.addX x₁ x₂ ℓ = ℓ ^ 2 - x₁ - x₂ := by
-- proof
  simp only [addX, IsShortNF.a₁, IsShortNF.a₂]; ring

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[shortNF_addY](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma shortNF_addY
  [Field F]
  {W' : WeierstrassCurve F}
  [W'.IsShortNF]
  {x₁ x₂ y₁ ℓ : F} :
-- imply
  W'.toAffine.addY x₁ x₂ y₁ ℓ = ℓ * (x₁ - W'.toAffine.addX x₁ x₂ ℓ) - y₁ := by
-- proof
  simp only [addY, negAddY, negY, addX, IsShortNF.a₁, IsShortNF.a₂, IsShortNF.a₃]; ring

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[shortNF_slope_of_X_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma shortNF_slope_of_X_ne
  [Field F]
  {W' : WeierstrassCurve F}
  [W'.IsShortNF]
  [DecidableEq F]
  {x₁ x₂ y₁ y₂ : F}
-- given
  (hx : x₁ ≠ x₂) :
-- imply
  W'.toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
-- proof
  slope_of_X_ne hx

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[shortNF_slope_of_tangent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma shortNF_slope_of_tangent
  [Field F]
  {W' : WeierstrassCurve F}
  [W'.IsShortNF]
  [DecidableEq F]
  {x₁ y₁ y₂ : F}
-- given
  (hy : y₁ ≠ W'.toAffine.negY x₁ y₂) :
-- imply
  W'.toAffine.slope x₁ x₁ y₁ y₂ = (3 * x₁ ^ 2 + W'.a₄) / (2 * y₁) := by
-- proof
  rw [slope_of_Y_ne rfl hy]
  congr 1
  · simp only [IsShortNF.a₂, IsShortNF.a₁]; ring
  · simp only [negY, IsShortNF.a₁, IsShortNF.a₃]; ring
end WeierstrassCurve.Affine
namespace WeierstrassCurve.Affine.Point
variable {F : Type*} [Field F] [DecidableEq F]
  {W' : WeierstrassCurve F} [W'.IsShortNF]


namespace WeierstrassCurve.Affine.Point

/--
[explicit_chord_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
lemma explicit_chord_formula
  [Field F]
  [DecidableEq F]
  {x₁ x₂ y₁ y₂ : F}
-- given
  (h₁ : W'.toAffine.Nonsingular x₁ y₁)
  (h₂ : W'.toAffine.Nonsingular x₂ y₂)
  (hx : x₁ ≠ x₂) :
-- imply
  let ℓ := W'.toAffine.slope x₁ x₂ y₁ y₂ let x₃ := W'.toAffine.addX x₁ x₂ ℓ ∃ h₃ : W'.toAffine.Nonsingular x₃ (W'.toAffine.addY x₁ x₂ y₁ ℓ), some _ _ h₁ + some _ _ h₂ = some x₃ (W'.toAffine.addY x₁ x₂ y₁ ℓ) h₃ ∧ ℓ = (y₁ - y₂) / (x₁ - x₂) ∧ x₃ = ℓ ^ 2 - x₁ - x₂ ∧ W'.toAffine.addY x₁ x₂ y₁ ℓ = ℓ * (x₁ - x₃) - y₁ := by
-- proof
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W'.toAffine.negY x₂ y₂) := fun h => hx h.1
  exact ⟨nonsingular_add h₁ h₂ hxy,
    add_some hxy,
    shortNF_slope_of_X_ne hx,
    shortNF_addX x₁ x₂ _,
    shortNF_addY x₁ x₂ y₁ _⟩
end WeierstrassCurve.Affine.Point
end Theorem_23_20
section Theorem_23_1
open ArithmeticGeometry

end WeierstrassCurve.Affine.Point

/--
[IsProjectiveVariety.complete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma complete_eq
  {k : Type u}
  [Field k]
  {V : Type u}
  [TopologicalSpace V]
  [h : IsProjectiveVariety k V] :
-- imply
  IsCompleteVariety V := by
-- proof
  apply IsProjectiveVariety.complete k V

/--
[WeierstrassCurve.exists_variableChange_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma exists_variableChange_a_eq
  [Field k]
  {W : WeierstrassCurve k}
-- given
  (hchar2 : (2 : k) ≠ 0)
  (hchar3 : (3 : k) ≠ 0) :
-- imply
  ∃ C : VariableChange k, (C • W).a₁ = 0 ∧ (C • W).a₂ = 0 ∧ (C • W).a₃ = 0 := by
-- proof
  apply WeierstrassCurve.exists_variableChange_a hchar2 hchar3 W

/--
[aut_s_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma aut_s_eq_zero_eq
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  {C : VariableChange F}
-- given
  (hC : C • W = W)
  (h2 : (2 : F) ≠ 0) :
-- imply
  C.s = 0 := by
-- proof
  apply WeierstrassCurve.aut_s_eq_zero hC h2

/--
[aut_r_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma aut_r_eq_zero_eq
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  {C : VariableChange F}
-- given
  (hC : C • W = W)
  (h2 : (2 : F) ≠ 0)
  (h3 : (3 : F) ≠ 0) :
-- imply
  C.r = 0 := by
-- proof
  apply WeierstrassCurve.aut_r_eq_zero hC h2 h3

/--
[aut_t_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma aut_t_eq_zero_eq
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  {C : VariableChange F}
-- given
  (hC : C • W = W)
  (h2 : (2 : F) ≠ 0)
  (h3 : (3 : F) ≠ 0) :
-- imply
  C.t = 0 := by
-- proof
  apply WeierstrassCurve.aut_t_eq_zero hC h2 h3

/--
[aut_u_inv_pow4_mul_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma aut_u_inv_pow4_mul_a_eq
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  {C : VariableChange F}
-- given
  (hC : C • W = W)
  (h2 : (2 : F) ≠ 0)
  (h3 : (3 : F) ≠ 0) :
-- imply
  (↑C.u⁻¹ : F) ^ 4 * W.a₄ = W.a₄ := by
-- proof
  apply WeierstrassCurve.aut_u_inv_pow4_mul_a hC h2 h3

/--
[aut_u_inv_pow6_mul_a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma aut_u_inv_pow6_mul_a_eq
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  {C : VariableChange F}
-- given
  (hC : C • W = W)
  (h2 : (2 : F) ≠ 0)
  (h3 : (3 : F) ≠ 0) :
-- imply
  (↑C.u⁻¹ : F) ^ 6 * W.a₆ = W.a₆ := by
-- proof
  apply WeierstrassCurve.aut_u_inv_pow6_mul_a hC h2 h3

/--
[aut_u_inv_pow4_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma aut_u_inv_pow4_eq_one_eq
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  {C : VariableChange F}
-- given
  (hC : C • W = W)
  (h2 : (2 : F) ≠ 0)
  (h3 : (3 : F) ≠ 0)
  (ha4 : W.a₄ ≠ 0) :
-- imply
  (↑C.u⁻¹ : F) ^ 4 = 1 := by
-- proof
  apply WeierstrassCurve.aut_u_inv_pow4_eq_one hC h2 h3 ha4

/--
[aut_u_inv_pow6_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma aut_u_inv_pow6_eq_one_eq
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  {C : VariableChange F}
-- given
  (hC : C • W = W)
  (h2 : (2 : F) ≠ 0)
  (h3 : (3 : F) ≠ 0)
  (ha6 : W.a₆ ≠ 0) :
-- imply
  (↑C.u⁻¹ : F) ^ 6 = 1 := by
-- proof
  apply WeierstrassCurve.aut_u_inv_pow6_eq_one hC h2 h3 ha6

/--
[a](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma a_eq
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  [W.IsElliptic] :
-- imply
  W.a₄ ≠ 0 ∨ W.a₆ ≠ 0 := by
-- proof
  apply WeierstrassCurve.a

/--
[u_pow_eq_one_of_inv_val_pow_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma u_pow_eq_one_of_inv_val_pow_eq_one_eq
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  {C : VariableChange F}
  {n : ℕ}
-- given
  (h : (↑C.u⁻¹ : F) ^ n = 1) :
-- imply
  C.u ^ n = 1 := by
-- proof
  apply WeierstrassCurve.u_pow_eq_one_of_inv_val_pow_eq_one h

/--
[autGroup_u_pow_twelve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma autGroup_u_pow_twelve_eq
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  [W.IsElliptic]
  {C : VariableChange F}
-- given
  (hC : C ∈ autGroup F W)
  (h2 : (2 : F) ≠ 0)
  (h3 : (3 : F) ≠ 0) :
-- imply
  C.u ^ 12 = 1 := by
-- proof
  apply WeierstrassCurve.autGroup_u_pow_twelve hC h2 h3

/--
[autGroup_u_pow4_eq_one_of_j_1728](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma autGroup_u_pow4_eq_one_of_j_1728_eq
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  [W.IsElliptic]
  {C : VariableChange F}
-- given
  (h2 : (2 : F) ≠ 0)
  (h3 : (3 : F) ≠ 0)
  (ha4 : W.a₄ ≠ 0)
  (hC : C ∈ autGroup F W) :
-- imply
  C.u ^ 4 = 1 ∧ C.r = 0 ∧ C.s = 0 ∧ C.t = 0 := by
-- proof
  apply WeierstrassCurve.autGroup_u_pow4_eq_one_of_j_1728 h2 h3 ha4 hC

/--
[autGroup_u_pow6_eq_one_of_j_0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma autGroup_u_pow6_eq_one_of_j_0_eq
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  [W.IsElliptic]
  {C : VariableChange F}
-- given
  (h2 : (2 : F) ≠ 0)
  (h3 : (3 : F) ≠ 0)
  (ha6 : W.a₆ ≠ 0)
  (hC : C ∈ autGroup F W) :
-- imply
  C.u ^ 6 = 1 ∧ C.r = 0 ∧ C.s = 0 ∧ C.t = 0 := by
-- proof
  apply WeierstrassCurve.autGroup_u_pow6_eq_one_of_j_0 h2 h3 ha6 hC

/--
[u_inv_val_pow_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma u_inv_val_pow_eq_one_eq
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  [W.IsElliptic]
  {n : ℕ}
  {u : Fˣ}
-- given
  (h : u ^ n = 1) :
-- imply
  (↑u⁻¹ : F) ^ n = 1 := by
-- proof
  apply WeierstrassCurve.u_inv_val_pow_eq_one h

/--
[fourth_root_mem_autGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma fourth_root_mem_autGroup_eq
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  [W.IsElliptic]
  {u : Fˣ}
-- given
  (hu : u ^ 4 = 1)
  (ha₆ : W.a₆ = 0) :
-- imply
  (⟨u, 0, 0, 0⟩ : VariableChange F) ∈ autGroup F W := by
-- proof
  apply WeierstrassCurve.fourth_root_mem_autGroup hu ha₆

/--
[sixth_root_mem_autGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/EllipticCurves.lean)
-/
@[path]
private lemma sixth_root_mem_autGroup_eq
  [Field F]
  {W : WeierstrassCurve F}
  [W.IsShortNF]
  [W.IsElliptic]
  {u : Fˣ}
-- given
  (hu : u ^ 6 = 1)
  (ha₄ : W.a₄ = 0) :
-- imply
  (⟨u, 0, 0, 0⟩ : VariableChange F) ∈ autGroup F W := by
-- proof
  apply WeierstrassCurve.sixth_root_mem_autGroup hu ha₄


-- created on 2026-10-23
