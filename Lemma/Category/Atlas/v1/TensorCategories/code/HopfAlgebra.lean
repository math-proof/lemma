import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.HopfAlgebra
open Coalgebra HopfAlgebra WithConv LinearMap
open scoped TensorProduct


/--
[Proposition_1_22_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
lemma Proposition_1_22_1
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [Semiring A]
  [HopfAlgebra R A] :
-- imply
  mul' R A ∘ₗ (antipode R).lTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit ∧ mul' R A ∘ₗ (antipode R).rTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit :=
-- proof
  ⟨HopfAlgebra.mul_antipode_lTensor_comul, HopfAlgebra.mul_antipode_rTensor_comul⟩
section AntipodeUniqueness

/--
[HopfAlgebra.antipode_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
lemma HopfAlgebra.antipode_unique
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [Semiring A]
  [Bialgebra R A]
  {S₁ S₂ : A →ₗ[R] A}
-- given
  (hS₁_left : mul' R A ∘ₗ S₁.rTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit)
  (hS₂_right : mul' R A ∘ₗ S₂.lTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit) :
-- imply
  S₁ = S₂ := by
-- proof
  have hS₁ : (toConv S₁ : WithConv (A →ₗ[R] A)) * toConv .id = 1 := by
    ext a; simp [convMul_apply, convOne_apply]; exact LinearMap.congr_fun hS₁_left a
  have hS₂ : toConv (.id : A →ₗ[R] A) * toConv S₂ = 1 := by
    ext a; simp [convMul_apply, convOne_apply]; exact LinearMap.congr_fun hS₂_right a
  have key : (toConv S₁ : WithConv (A →ₗ[R] A)) = toConv S₂ :=
    calc toConv S₁
      = toConv S₁ * 1 := (mul_one _).symm
      _ = toConv S₁ * (toConv .id * toConv S₂) := by rw [hS₂]
      _ = (toConv S₁ * toConv .id) * toConv S₂ := (mul_assoc _ _ _).symm
      _ = 1 * toConv S₂ := by rw [hS₁]
      _ = toConv S₂ := one_mul _
  exact toConv_injective key
end AntipodeUniqueness

/--
[Proposition_1_22_4](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
lemma Proposition_1_22_4
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [Semiring A]
  [Bialgebra R A]
  {S₁ S₂ : A →ₗ[R] A}
-- given
  (hS₁_left : mul' R A ∘ₗ S₁.rTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit)
  (hS₂_right : mul' R A ∘ₗ S₂.lTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit) :
-- imply
  S₁ = S₂ :=
-- proof
  HopfAlgebra.antipode_unique S₁ S₂ hS₁_left hS₂_right
section AntipodeAntiHom
noncomputable section
variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]

/--
[HopfAlgebra.antipode_sq_eq_id_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
lemma HopfAlgebra.antipode_sq_eq_id_comm
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [CommSemiring A]
  [HopfAlgebra R A]
  {a : A} :
-- imply
  antipode R (antipode R a) = a := by
-- proof
  have h_SS_conv_S : (toConv ((antipode R).comp (antipode R)) : WithConv (A →ₗ[R] A)) *
    toConv (antipode R) = 1 := by
    ext x
    simp only [convMul_apply, convOne_apply]
    have := mul_antipode_rTensor_comul_apply (R := R) x
    have h_apply_S : antipode R (mul' R A ((antipode R).rTensor A (comul x))) =
      antipode R (algebraMap R A (counit (R := R) x)) := congr_arg _ this
    rw [Algebra.algebraMap_eq_smul_one, map_smul, HopfAlgebra.antipode_one] at h_apply_S
    rw [Algebra.algebraMap_eq_smul_one]
    have S_comp_mul : (antipode R).comp (mul' R A) =
      (mul' R A).comp (TensorProduct.map (antipode R) (antipode R)) := by
      ext a b
      simp [mul'_apply, HopfAlgebra.antipode_mul_comm]
    change mul' R A (TensorProduct.map ((antipode R).comp (antipode R)) (antipode R) (comul x)) =
      counit x • 1
    rw [show TensorProduct.map ((antipode R).comp (antipode R)) (antipode R) =
      (TensorProduct.map (antipode R) (antipode R)).comp ((antipode R).rTensor A) from by
      ext a b; simp]
    rwa [comp_apply, ← comp_apply (mul' R A), ← S_comp_mul, comp_apply]
  have h_id_conv_S : (toConv (.id : A →ₗ[R] A)) * toConv (antipode R) = 1 :=
    HopfAlgebra.id_conv_antipode
  have key : (toConv ((antipode R).comp (antipode R)) : WithConv (A →ₗ[R] A)) = toConv .id :=
    calc toConv ((antipode R).comp (antipode R))
      = toConv ((antipode R).comp (antipode R)) * 1 := (mul_one _).symm
      _ = toConv ((antipode R).comp (antipode R)) *
        (toConv (antipode R) * toConv (.id : A →ₗ[R] A)) := by
        rw [HopfAlgebra.antipode_conv_id]
      _ = (toConv ((antipode R).comp (antipode R)) * toConv (antipode R)) *
        toConv .id := (mul_assoc _ _ _).symm
      _ = 1 * toConv .id := by rw [h_SS_conv_S]
      _ = toConv .id := one_mul _
  have key' : (antipode R).comp (antipode R) = (.id : A →ₗ[R] A) := toConv_injective key
  exact LinearMap.congr_fun key' a
end
section ConvolutionLemmas
variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

/--
[HopfAlgebra.sum_antimul_mul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
lemma HopfAlgebra.sum_antimul_mul_eq
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [Semiring A]
  [HopfAlgebra R A]
  {a b : A}
  {ra : Coalgebra.Repr R a}
  {rb : Coalgebra.Repr R b} :
-- imply
  ∑ i ∈ ra.index, ∑ j ∈ rb.index, (antipode R (rb.left j) * antipode R (ra.left i)) * (ra.right i * rb.right j) = algebraMap R A (counit a * counit b) := by
-- proof
  conv_lhs =>
    arg 2; ext i; arg 2; ext j
    rw [show (antipode R (rb.left j) * antipode R (ra.left i)) * (ra.right i * rb.right j) =
      antipode R (rb.left j) * (antipode R (ra.left i) * ra.right i) * rb.right j
      from by simp [mul_assoc]]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext j; arg 2; ext i
    rw [mul_assoc (antipode R (rb.left j))]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_antipode_mul_eq_algebraMap_counit ra]
  simp_rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]
  rw [← Finset.smul_sum, sum_antipode_mul_eq_smul rb]
  simp [smul_smul, mul_comm (counit (R := R) a)]

/--
[HopfAlgebra.sum_mul_antimul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
lemma HopfAlgebra.sum_mul_antimul_eq
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [Semiring A]
  [HopfAlgebra R A]
  {a b : A}
  {ra : Coalgebra.Repr R a}
  {rb : Coalgebra.Repr R b} :
-- imply
  ∑ i ∈ ra.index, ∑ j ∈ rb.index, (ra.left i * rb.left j) * (antipode R (rb.right j) * antipode R (ra.right i)) = algebraMap R A (counit a * counit b) := by
-- proof
  conv_lhs =>
    arg 2; ext i; arg 2; ext j
    rw [show (ra.left i * rb.left j) * (antipode R (rb.right j) * antipode R (ra.right i)) =
      ra.left i * (rb.left j * antipode R (rb.right j)) * antipode R (ra.right i)
      from by simp [mul_assoc]]
  conv_lhs =>
    arg 2; ext i; arg 2; ext j
    rw [mul_assoc (ra.left i)]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_mul_antipode_eq_algebraMap_counit rb]
  simp_rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]
  rw [← Finset.smul_sum, sum_mul_antipode_eq_smul ra]
  simp [smul_smul, mul_comm (counit (R := R) b)]
end ConvolutionLemmas
section AntipodeAntiHomGeneral
noncomputable section
variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

/--
[HopfAlgebra.Smul_conv_mul_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
lemma HopfAlgebra.Smul_conv_mul_general
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [Semiring A]
  [HopfAlgebra R A] :
-- imply
  (toConv ((antipode R).comp (mul' R A)) : WithConv (A ⊗[R] A →ₗ[R] A)) * toConv (mul' R A) = 1 := by
-- proof
  have key : ∀ (a b : A),
    (mul' R A) (TensorProduct.map ((antipode R).comp (mul' R A)) (mul' R A)
      (comul (a ⊗ₜ[R] b))) =
    algebraMap R A (counit (a ⊗ₜ[R] b)) := by
    intro a b
    obtain ⟨sa, hsa⟩ := TensorProduct.exists_finset (R := R) (M := A) (N := A) (comul (R := R) a)
    obtain ⟨sb, hsb⟩ := TensorProduct.exists_finset (R := R) (M := A) (N := A) (comul (R := R) b)
    rw [TensorProduct.comul_def, comp_apply, TensorProduct.AlgebraTensorModule.map_tmul, hsa, hsb]
    simp only [TensorProduct.tmul_sum, TensorProduct.sum_tmul, map_sum,
      LinearEquiv.coe_coe,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      TensorProduct.map_tmul, comp_apply, mul'_apply]
    have hopf := mul_antipode_rTensor_comul_apply (R := R) (a * b)
    rw [Bialgebra.comul_mul, hsa, hsb] at hopf
    simp only [Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
      map_sum, rTensor_tmul, mul'_apply] at hopf
    rw [hopf]
    congr 1
    rw [TensorProduct.counit_tmul, Bialgebra.counit_mul, Algebra.smul_def]
    simp [mul_comm]
  ext a b
  simp only [TensorProduct.AlgebraTensorModule.curry_apply]
  exact key a b

/--
[HopfAlgebra.antimul_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
lemma HopfAlgebra.antimul_tmul
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [Semiring A]
  [HopfAlgebra R A]
  {a b : A} :
-- imply
  HopfAlgebra.antimul (a ⊗ₜ[R] b) = antipode R b * antipode R a := by
-- proof
  simp [HopfAlgebra.antimul, mul'_apply]

/--
[HopfAlgebra.mul_conv_antimul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
lemma HopfAlgebra.mul_conv_antimul
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [Semiring A]
  [HopfAlgebra R A] :
-- imply
  (toConv (mul' R A) : WithConv (A ⊗[R] A →ₗ[R] A)) * toConv (HopfAlgebra.antimul (R := R) (A := A)) = 1 := by
-- proof
  have key : ∀ (a b : A),
    (mul' R A) (TensorProduct.map (mul' R A) (HopfAlgebra.antimul (R := R) (A := A))
      (comul (R := R) (a ⊗ₜ[R] b))) =
    algebraMap R A (counit (R := R) (a ⊗ₜ[R] b)) := by
    intro a b
    obtain ⟨sa, hsa⟩ := TensorProduct.exists_finset (R := R) (M := A) (N := A) (comul (R := R) a)
    obtain ⟨sb, hsb⟩ := TensorProduct.exists_finset (R := R) (M := A) (N := A) (comul (R := R) b)
    rw [TensorProduct.comul_def, comp_apply, TensorProduct.AlgebraTensorModule.map_tmul, hsa, hsb]
    simp only [TensorProduct.tmul_sum, TensorProduct.sum_tmul, map_sum,
      LinearEquiv.coe_coe,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      TensorProduct.map_tmul, mul'_apply, HopfAlgebra.antimul_tmul]
    let ra : Coalgebra.Repr R a := ⟨sa, Prod.fst, Prod.snd, hsa.symm⟩
    let rb : Coalgebra.Repr R b := ⟨sb, Prod.fst, Prod.snd, hsb.symm⟩
    rw [TensorProduct.counit_tmul, smul_eq_mul, mul_comm (counit (R := R) b)]
    rw [Finset.sum_comm]
    exact HopfAlgebra.sum_mul_antimul_eq ra rb
  ext a b
  simp only [TensorProduct.AlgebraTensorModule.curry_apply]
  exact key a b

/--
[HopfAlgebra.antipode_mul_anti](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
lemma HopfAlgebra.antipode_mul_anti
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [Semiring A]
  [HopfAlgebra R A]
  {a b : A} :
-- imply
  antipode R (a * b) = antipode R b * antipode R a := by
-- proof
  have h_eq : (toConv ((antipode R).comp (mul' R A)) : WithConv (A ⊗[R] A →ₗ[R] A)) =
    toConv (HopfAlgebra.antimul (R := R) (A := A)) :=
    calc toConv ((antipode R).comp (mul' R A))
      = toConv ((antipode R).comp (mul' R A)) * 1 := (mul_one _).symm
      _ = toConv ((antipode R).comp (mul' R A)) *
        (toConv (mul' R A) * toConv (HopfAlgebra.antimul (R := R) (A := A))) := by
        rw [HopfAlgebra.mul_conv_antimul]
      _ = (toConv ((antipode R).comp (mul' R A)) * toConv (mul' R A)) *
        toConv (HopfAlgebra.antimul (R := R) (A := A)) := (mul_assoc _ _ _).symm
      _ = 1 * toConv (HopfAlgebra.antimul (R := R) (A := A)) := by
        rw [HopfAlgebra.Smul_conv_mul_general]
      _ = toConv (HopfAlgebra.antimul (R := R) (A := A)) := one_mul _
  have h_eq' := toConv_injective h_eq
  have := LinearMap.congr_fun h_eq' (a ⊗ₜ[R] b)
  simp [HopfAlgebra.antimul_tmul, mul'_apply] at this
  exact this
end
end AntipodeAntiHomGeneral

/-- The antipode of a Hopf algebra is a coalgebra antihomomorphism: `Δ ∘ S = τ ∘ (S ⊗ S) ∘ Δ`.
This is part of Proposition 1.22.5. -/
section Proposition_1_22_5_consolidated
variable (R : Type u) [CommSemiring R] (A : Type v) [Semiring A] [HopfAlgebra R A]
open Coalgebra HopfAlgebra LinearMap in

/-- Proposition 1.22.5: the antipode `S` on a bialgebra `H` is an antihomomorphism of
algebras with unit and of coalgebras with counit. Packaged as a fourfold conjunction
covering antimultiplicativity, unit preservation, anti-comultiplicativity, and counit
preservation. -/
end Proposition_1_22_5_consolidated
section DualAction
variable {k : Type u} [CommSemiring k] {H : Type v} [Semiring H] [Algebra k H] [HopfAlgebra k H]
variable {V : Type v} [AddCommGroup V] [Module k V] [Module H V] [SMulCommClass k H V]

/--
[Proposition_1_22_15_algebra_anti](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
lemma Proposition_1_22_15_algebra_anti
  {R : Type u}
  [CommSemiring R]
  {A : Type v}
  [Semiring A]
  [HopfAlgebra R A] :
-- imply
  ∀ (a b : A), HopfAlgebra.antipode R (a * b) = HopfAlgebra.antipode R b * HopfAlgebra.antipode R a :=
-- proof
  HopfAlgebra.antipode_mul_anti

/-- Coalgebra-antihomomorphism part of Proposition 1.22.15 / 1.22.5:
`Δ ∘ S = τ ∘ (S ⊗ S) ∘ Δ`. -/

/-- Descent step: if the iterated ranges of `S` stabilize at index `m`, then they already
agreed at index `m - 1`. Used to prove `S` is surjective on a finite-dimensional Hopf algebra. -/

/--
[HopfAlgebra.antipode_conv_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
private lemma antipode_conv_id_eq
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [Semiring A]
  [HopfAlgebra R A] :
-- imply
  (toConv (antipode R) : WithConv (A →ₗ[R] A)) * toConv .id = 1 := by
-- proof
  apply HopfAlgebra.antipode_conv_id

/--
[HopfAlgebra.id_conv_antipode](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
private lemma id_conv_antipode_eq
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [Semiring A]
  [HopfAlgebra R A] :
-- imply
  (toConv (.id : A →ₗ[R] A)) * toConv (antipode R) = 1 := by
-- proof
  apply HopfAlgebra.id_conv_antipode

/--
[HopfAlgebra.antimulComm_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
private lemma antimulComm_tmul_eq
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [CommSemiring A]
  [HopfAlgebra R A]
  {a b : A} :
-- imply
  HopfAlgebra.antimulComm (a ⊗ₜ[R] b) = antipode R a * antipode R b := by
-- proof
  apply HopfAlgebra.antimulComm_tmul a b

/--
[lmul'_comp_map_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
private lemma lmul'_comp_map_id_eq
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [CommSemiring A]
  [HopfAlgebra R A] :
-- imply
  (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toLinearMap.comp (TensorProduct.map (.id : A →ₗ[R] A) .id) = mul' R A := by
-- proof
  apply lmul'_comp_map_id

/--
[lmul'_comp_unit_tensor_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
private lemma lmul'_comp_unit_tensor_unit_eq
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [CommSemiring A]
  [HopfAlgebra R A] :
-- imply
  (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toLinearMap.comp (TensorProduct.map (Algebra.linearMap R A ∘ₗ counit) (Algebra.linearMap R A ∘ₗ counit)) = Algebra.linearMap R A ∘ₗ (counit : A ⊗[R] A →ₗ[R] R) := by
-- proof
  apply lmul'_comp_unit_tensor_unit

/--
[HopfAlgebra.antimulComm_conv_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
private lemma antimulComm_conv_mul_eq
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [CommSemiring A]
  [HopfAlgebra R A] :
-- imply
  (toConv HopfAlgebra.antimulComm : WithConv (A ⊗[R] A →ₗ[R] A)) * toConv (mul' R A) = 1 := by
-- proof
  apply HopfAlgebra.antimulComm_conv_mul

/--
[HopfAlgebra.mul_conv_antimulComm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
private lemma mul_conv_antimulComm_eq
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [CommSemiring A]
  [HopfAlgebra R A] :
-- imply
  (toConv (mul' R A) : WithConv (A ⊗[R] A →ₗ[R] A)) * toConv HopfAlgebra.antimulComm = 1 := by
-- proof
  apply HopfAlgebra.mul_conv_antimulComm

/--
[HopfAlgebra.Smul_conv_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
private lemma Smul_conv_mul_eq
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [CommSemiring A]
  [HopfAlgebra R A] :
-- imply
  (toConv ((antipode R).comp (mul' R A)) : WithConv (A ⊗[R] A →ₗ[R] A)) * toConv (mul' R A) = 1 := by
-- proof
  apply HopfAlgebra.Smul_conv_mul

/--
[HopfAlgebra.antipode_mul_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean)
-/
@[path]
private lemma antipode_mul_comm_eq
  {R : Type u}
  {A : Type v}
  [CommSemiring R]
  [CommSemiring A]
  [HopfAlgebra R A]
  {a b : A} :
-- imply
  antipode R (a * b) = antipode R a * antipode R b := by
-- proof
  apply HopfAlgebra.antipode_mul_comm a b


-- created on 2026-10-23
