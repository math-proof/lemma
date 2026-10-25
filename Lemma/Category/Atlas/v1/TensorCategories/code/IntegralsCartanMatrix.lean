import Mathlib
import sympy.Basic
import Structure.v1.Atlas.TensorCategories.code.IntegralsCartanMatrix.Part2
open Coalgebra
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory MonoidalCategory
open CategoryTheory


/--
[det_eq_zero_of_mulVec_eq_zero_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma det_eq_zero_of_mulVec_eq_zero_of_ne_zero
  {k : Type w}
  [Field k]
  [Fintype ι]
  [DecidableEq ι]
  {M : Matrix ι ι k}
  {d : ι → k}
-- given
  (hd : d ≠ 0)
  (hMd : M.mulVec d = 0) :
-- imply
  M.det = 0 := by
-- proof
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  exact ⟨d, hd, hMd⟩

/--
[cartan_matrix_degenerate_of_dim_vanishes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma cartan_matrix_degenerate_of_dim_vanishes
  {k : Type w}
  [Field k]
  [Fintype ι]
  [DecidableEq ι]
  {C_mat : ι → ι → ℕ}
  {d : ι → k}
-- given
  (hd_ne : d ≠ 0)
  (hd_kernel : ∀ i : ι, ∑ j : ι, (C_mat i j : k) * d j = 0) :
-- imply
  (cartanMatrixOverField C_mat : Matrix ι ι k).det = 0 := by
-- proof
  apply det_eq_zero_of_mulVec_eq_zero_of_ne_zero _ d hd_ne
  ext i
  simp only [Matrix.mulVec, dotProduct, cartanMatrixOverField, Matrix.of_apply, Pi.zero_apply]
  exact hd_kernel i

/--
[cartan_matrix_transpose_degenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma cartan_matrix_transpose_degenerate
  {k : Type w}
  [Field k]
  [Fintype ι]
  [DecidableEq ι]
  {C_mat : ι → ι → ℕ}
-- given
  (hdet : (cartanMatrixOverField C_mat : Matrix ι ι k).det = 0) :
-- imply
  (cartanMatrixOverField C_mat : Matrix ι ι k).transpose.det = 0 := by
-- proof
  rwa [Matrix.det_transpose]
section CategoricalUnimodularity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {C : Type u} [Category.{v} C]

/--
[IsUnimodularCategory.get_distinguished_iso_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma IsUnimodularCategory.get_distinguished_iso_unit
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  [HasDistinguishedInvertibleData C]
  [h : IsUnimodularCategory C] :
-- imply
  Nonempty (HasDistinguishedInvertibleData.distinguished (C := C) ≅ 𝟙_ C) :=
-- proof
  h.distinguished_iso_unit

/--
[isUnimodularCategory_of_pivotal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma isUnimodularCategory_of_pivotal
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  [HasDistinguishedInvertibleData C]
-- given
  (h : Nonempty (HasDistinguishedInvertibleData.distinguished (C := C) ≅ 𝟙_ C)) :
-- imply
  IsUnimodularCategory C :=
-- proof
  ⟨h⟩
end CategoricalUnimodularity
section PivotalDimensionTheorem
open CategoryTheory MonoidalCategory
variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/--
[dim_proj_zero_of_not_semisimple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma dim_proj_zero_of_not_semisimple
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {u : PivotalStructureData C}
  {φ : (𝟙_ C ⟶ 𝟙_ C) → k}
  {P : C}
  [Projective P]
-- given
  (h_retract : ∀ (P : C) [Projective P], φ (pivotalDim C u P) ≠ 0 → Projective (𝟙_ C))
  (hns : ¬ Projective (𝟙_ C)) :
-- imply
  φ (pivotalDim C u P) = 0 := by
-- proof
  by_contra h
  exact hns (h_retract P h)
section Theorem1531
open CategoryTheory MonoidalCategory
variable {k : Type w} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
[dim_vec_ne_zero_of_component_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma dim_vec_ne_zero_of_component_ne_zero
  {k : Type w}
  [Field k]
  [Fintype ι]
  [DecidableEq ι]
  [Field k]
  {d : ι → k}
  {i₀ : ι}
-- given
  (hi₀ : d i₀ ≠ 0) :
-- imply
  d ≠ 0 := by
-- proof
  intro h
  exact hi₀ (congr_fun h i₀)

/--
[theorem_1_53_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma theorem_1_53_1
  {k : Type w}
  [Field k]
  [Fintype ι]
  [DecidableEq ι]
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {u : PivotalStructureData C}
  {L : ι → C}
  {i₀ : ι}
  {P : ι → C}
  [hProj : ∀ i, Projective (P i)]
  {C_mat : ι → ι → ℕ}
  {φ : (𝟙_ C ⟶ 𝟙_ C) → k}
-- given
  (hns : ¬ Projective (𝟙_ C))
  (h_unit : Nonempty (L i₀ ≅ 𝟙_ C))
  (h_retract : ∀ (Q : C) [Projective Q], φ (pivotalDim C u Q) ≠ 0 → Projective (𝟙_ C))
  (h_dim_unit : φ (pivotalDim C u (𝟙_ C)) ≠ 0)
  (h_dim_iso : ∀ (X Y : C), Nonempty (X ≅ Y) → pivotalDim C u X = pivotalDim C u Y)
  (h_additive : ∀ i, ∑ j : ι, (C_mat i j : k) * φ (pivotalDim C u (L j)) = φ (pivotalDim C u (P i))) :
-- imply
  (cartanMatrixOverField C_mat : Matrix ι ι k).det = 0 := by
-- proof
  let d : ι → k := fun j => φ (pivotalDim C u (L j))
  have hdP : ∀ i, φ (pivotalDim C u (P i)) = 0 :=
    fun i => dim_proj_zero_of_not_semisimple u φ h_retract hns (P i)
  have hkernel : ∀ i, ∑ j : ι, (C_mat i j : k) * d j = 0 := by
    intro i
    rw [h_additive i]
    exact hdP i
  have hdi₀ : d i₀ ≠ 0 := by
    intro h
    apply h_dim_unit
    rwa [← h_dim_iso (L i₀) (𝟙_ C) h_unit]
  exact cartan_matrix_degenerate_of_dim_vanishes C_mat d
    (dim_vec_ne_zero_of_component_ne_zero d i₀ hdi₀) hkernel

/--
[Theorem_1_53_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma Theorem_1_53_1
  {k : Type w}
  [Field k]
  [Fintype ι]
  [DecidableEq ι]
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [RigidCategory C]
  {u : PivotalStructureData C}
  {L : ι → C}
  {i₀ : ι}
  {P : ι → C}
  [hProj : ∀ i, Projective (P i)]
  {C_mat : ι → ι → ℕ}
  {φ : (𝟙_ C ⟶ 𝟙_ C) → k}
-- given
  (hns : ¬ Projective (𝟙_ C))
  (h_unit : Nonempty (L i₀ ≅ 𝟙_ C))
  (h_retract : ∀ (Q : C) [Projective Q], φ (pivotalDim C u Q) ≠ 0 → Projective (𝟙_ C))
  (h_dim_unit : φ (pivotalDim C u (𝟙_ C)) ≠ 0)
  (h_dim_iso : ∀ (X Y : C), Nonempty (X ≅ Y) → pivotalDim C u X = pivotalDim C u Y)
  (h_additive : ∀ i, ∑ j : ι, (C_mat i j : k) * φ (pivotalDim C u (L j)) = φ (pivotalDim C u (P i))) :
-- imply
  (cartanMatrixOverField C_mat : Matrix ι ι k).det = 0 :=
-- proof
  theorem_1_53_1 u hns L i₀ h_unit P C_mat φ h_retract h_dim_unit h_dim_iso h_additive
end Theorem1531
section Proposition1523
variable (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H] [Coalgebra k H]

/--
[Proposition_1_52_3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma Proposition_1_52_3
  {k : Type u}
  [Field k]
  {H : Type v}
  [Ring H]
  [Algebra k H]
  [Coalgebra k H]
  [FiniteDimensional k H] :
-- imply
  (∃ (I₀ : H), IsLeftIntegral k H I₀ ∧ I₀ ≠ 0 ∧ ∀ (J : H), IsLeftIntegral k H J → ∃ (c : k), J = c • I₀) ∧ (∃ (I₀ : H), IsRightIntegral k H I₀ ∧ I₀ ≠ 0 ∧ ∀ (J : H), IsRightIntegral k H J → ∃ (c : k), J = c • I₀) :=
-- proof
  ⟨prop_1_52_3_left k H, prop_1_52_3_right k H⟩

/--
[Proposition_1_52_3_left_integral_space_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma Proposition_1_52_3_left_integral_space_dim
  {k : Type u}
  [Field k]
  {H : Type v}
  [Ring H]
  [Algebra k H]
  [Coalgebra k H]
  [FiniteDimensional k H] :
-- imply
  Module.finrank k (leftIntSubmodule k H) = 1 :=
-- proof
  frobenius_leftIntSubmodule_finrank_one k H

/--
[Proposition_1_52_3_right_integral_space_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma Proposition_1_52_3_right_integral_space_dim
  {k : Type u}
  [Field k]
  {H : Type v}
  [Ring H]
  [Algebra k H]
  [Coalgebra k H]
  [FiniteDimensional k H] :
-- imply
  Module.finrank k (rightIntSubmodule k H) = 1 :=
-- proof
  frobenius_rightIntSubmodule_finrank_one k H

/--
[Proposition_1_52_3_integral_space_dims](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma Proposition_1_52_3_integral_space_dims
  {k : Type u}
  [Field k]
  {H : Type v}
  [Ring H]
  [Algebra k H]
  [Coalgebra k H]
  [FiniteDimensional k H] :
-- imply
  Module.finrank k (leftIntSubmodule k H) = 1 ∧ Module.finrank k (rightIntSubmodule k H) = 1 :=
-- proof
  ⟨frobenius_leftIntSubmodule_finrank_one k H,
    frobenius_rightIntSubmodule_finrank_one k H⟩
end Proposition1523
section Proposition1524
open CategoryTheory
variable (k : Type w) [Field k] (H : Type w) [Ring H] [Algebra k H] [Coalgebra k H]

/--
[Proposition_1_52_4](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma Proposition_1_52_4
  {k : Type w}
  [Field k]
  {H : Type w}
  [Ring H]
  [Algebra k H]
  [Coalgebra k H]
  [Category C]
  [MonoidalCategory C]
  [RigidCategory C]
  [HasDistinguishedInvertibleData C]
  [FiniteDimensional k H]
  [inst : Prop1524RepData k H C]
  {I : H}
  {dc : DistinguishedCharacter k H I}
-- given
  (hI : I ≠ 0) :
-- imply
  Nonempty (HasDistinguishedInvertibleData.distinguished (C := C) ≅ inst.oneDimChar dc.χ) :=
-- proof
  inst.lρ_iso_distinguishedChar I hI dc

/--
[Proposition_1_52_4_unimodular_implies_char_eq_counit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma Proposition_1_52_4_unimodular_implies_char_eq_counit
  {k : Type w}
  [Field k]
  {H : Type w}
  [Ring H]
  [Algebra k H]
  [Coalgebra k H]
  {I : H}
  {dc : DistinguishedCharacter k H I}
-- given
  (hI_ne : I ≠ 0)
  (huni : IsUnimodularAlgebra k H) :
-- imply
  ∀ x : H, dc.χ x = Coalgebra.counit (R := k) x :=
-- proof
  distinguished_char_eq_counit_of_unimodular k H I dc hI_ne huni

/--
[Proposition_1_52_4_char_eq_counit_implies_right_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma Proposition_1_52_4_char_eq_counit_implies_right_integral
  {k : Type w}
  [Field k]
  {H : Type w}
  [Ring H]
  [Algebra k H]
  [Coalgebra k H]
  {I : H}
  {dc : DistinguishedCharacter k H I}
-- given
  (hχε : ∀ x : H, dc.χ x = Coalgebra.counit (R := k) x) :
-- imply
  IsRightIntegral k H I :=
-- proof
  left_integral_is_right_of_char_eq_counit k H I dc hχε
end Proposition1524
section IntegralCointegralPairing
open scoped TensorProduct
variable (k : Type w) [Field k] (H : Type w) [Ring H] [Algebra k H] [Coalgebra k H]

/--
[exists_idempotent_integral_of_semisimple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma exists_idempotent_integral_of_semisimple
  {k : Type u}
  [Field k]
  {H : Type v}
  [Ring H]
  [Algebra k H]
  [Coalgebra k H]
  [FiniteDimensional k H]
-- given
  (hss : IsSemisimpleRing H) :
-- imply
  ∃ (J : H), IsLeftIntegral k H J ∧ J * J = J ∧ J ≠ 0 := by
-- proof
  obtain ⟨I₀, hI₀int, hI₀ne, _⟩ := prop_1_52_3_left k H
  let L : Submodule H H := Submodule.span H {I₀}
  have hL_ne : L ≠ ⊥ := by
    intro h; apply hI₀ne
    have : I₀ ∈ L := Submodule.mem_span_singleton_self I₀
    rw [h] at this; exact (Submodule.mem_bot H).mp this
  obtain ⟨M, hLM⟩ := ComplementedLattice.exists_isCompl L
  let π : H →ₗ[H] H := L.subtype ∘ₗ L.linearProjOfIsCompl M hLM
  let e : H := π (1 : H)
  have hπ_app : ∀ h : H, π h = h * e := by
    intro h
    have := π.map_smul h (1 : H)
    simp only [smul_eq_mul, mul_one] at this
    exact this
  have he_mem : e ∈ L := SetLike.coe_mem _
  have he_idem : e * e = e := by
    have hidem : ∀ x, π (π x) = π x := by
      intro x
      show L.subtype (L.linearProjOfIsCompl M hLM (L.subtype (L.linearProjOfIsCompl M hLM x))) =
        L.subtype (L.linearProjOfIsCompl M hLM x)
      congr 1; exact Submodule.linearProjOfIsCompl_apply_left hLM _
    rw [(hπ_app e).symm, show π e = π (π 1) from rfl, hidem 1]
  have he_ne : e ≠ 0 := by
    intro he0; apply hL_ne; rw [eq_bot_iff]
    intro x hx
    have hπx : π x = 0 := by
      calc π x = x * e := hπ_app x
        _ = x * 0 := by rw [he0]
        _ = 0 := mul_zero x
    have : (L.linearProjOfIsCompl M hLM x : H) = x := by
      simp [Submodule.linearProjOfIsCompl_apply_left hLM ⟨x, hx⟩]
    rw [show π x = (L.linearProjOfIsCompl M hLM x : H) from rfl] at hπx
    rw [this] at hπx; simp [hπx]
  have he_scalar : ∃ c : k, e = c • I₀ := by
    rw [show L = Submodule.span H {I₀} from rfl] at he_mem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp he_mem
    exact ⟨Coalgebra.counit (R := k) a, by rw [← hI₀int.left_integral a]; exact ha.symm⟩
  obtain ⟨c, hc⟩ := he_scalar
  have he_int : IsLeftIntegral k H e := by
    rw [hc]
    exact ⟨fun x => by rw [mul_smul_comm, hI₀int.left_integral x, smul_comm]⟩
  exact ⟨e, he_int, he_idem, he_ne⟩

/--
[counit_ne_zero_of_exists_idempotent_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsCartanMatrix.lean)
-/
@[path]
lemma counit_ne_zero_of_exists_idempotent_integral
  {k : Type u}
  [Field k]
  {H : Type v}
  [Ring H]
  [Algebra k H]
  [Coalgebra k H]
  [FiniteDimensional k H]
  {I : H}
-- given
  (hI : IsLeftIntegral k H I)
  (hne : I ≠ 0)
  (hex : ∃ (J : H), IsLeftIntegral k H J ∧ J * J = J ∧ J ≠ 0) :
-- imply
  Coalgebra.counit (R := k) I ≠ 0 := by
-- proof
  obtain ⟨J, hJint, hJidem, hJne⟩ := hex
  have hJsq : J * J ≠ 0 := by rwa [hJidem]
  have hεJ : Coalgebra.counit (R := k) J ≠ 0 :=
    counit_ne_zero_of_sq_ne_zero hJint hJsq
  obtain ⟨I₀, hI₀int, _, hI₀uniq⟩ := prop_1_52_3_left k H
  obtain ⟨d, rfl⟩ := hI₀uniq I hI
  obtain ⟨c, rfl⟩ := hI₀uniq J hJint
  simp only [map_smul, smul_eq_mul] at hεJ ⊢
  exact mul_ne_zero (by intro hd; exact hne (by simp [hd]))
    (by intro hI₀; exact hεJ (by rw [hI₀, mul_zero]))
/-- Proposition 1.52.5: for a nonzero left integral `I` in a finite dimensional quasi-Hopf
algebra, semisimplicity of `H` is equivalent to `ε I ≠ 0`, equivalent to `I * I ≠ 0`,
equivalent to the existence of a nonzero idempotent left integral. -/


-- created on 2026-10-23
