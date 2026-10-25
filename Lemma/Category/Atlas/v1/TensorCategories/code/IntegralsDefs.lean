import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.TensorCategories.code.IntegralsDefs
open Coalgebra
open scoped TensorProduct
open CategoryTheory MonoidalCategory
open CategoryTheory


/--
[isLeftIntegral_iff_def_1_52_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma isLeftIntegral_iff_def_1_52_1
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [Coalgebra R H]
  {I : H} :
-- imply
  IsLeftIntegral R H I ↔ Def_1_52_1_IsLeftIntegral R H I :=
-- proof
  ⟨fun h => h.left_integral, fun h => ⟨h⟩⟩

/--
[isRightIntegral_iff_def_1_52_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma isRightIntegral_iff_def_1_52_1
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [Coalgebra R H]
  {I : H} :
-- imply
  IsRightIntegral R H I ↔ Def_1_52_1_IsRightIntegral R H I :=
-- proof
  ⟨fun h => h.right_integral, fun h => ⟨h⟩⟩
section IntegralProperties
variable {R : Type u} [CommSemiring R] {H : Type v} [Semiring H] [Algebra R H] [Coalgebra R H]

/--
[isLeftIntegral_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma isLeftIntegral_zero
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [Coalgebra R H] :
-- imply
  IsLeftIntegral R H (0 : H) :=
-- proof
  ⟨fun _ => by simp⟩

/--
[isRightIntegral_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma isRightIntegral_zero
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [Coalgebra R H] :
-- imply
  IsRightIntegral R H (0 : H) :=
-- proof
  ⟨fun _ => by simp⟩

/--
[IsLeftIntegral.smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma IsLeftIntegral.smul
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [Coalgebra R H]
  {I : H}
  {r : R}
-- given
  (hI : IsLeftIntegral R H I) :
-- imply
  IsLeftIntegral R H (r • I) :=
-- proof
  ⟨fun x => by rw [mul_smul_comm, hI.left_integral x, smul_comm]⟩

/--
[IsRightIntegral.smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma IsRightIntegral.smul
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [Coalgebra R H]
  {I : H}
  {r : R}
-- given
  (hI : IsRightIntegral R H I) :
-- imply
  IsRightIntegral R H (r • I) :=
-- proof
  ⟨fun x => by rw [smul_mul_assoc, hI.right_integral x, smul_comm]⟩

/--
[IsLeftIntegral.add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma IsLeftIntegral.add
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [Coalgebra R H]
  {I J : H}
-- given
  (hI : IsLeftIntegral R H I)
  (hJ : IsLeftIntegral R H J) :
-- imply
  IsLeftIntegral R H (I + J) :=
-- proof
  ⟨fun x => by rw [mul_add, hI.left_integral x, hJ.left_integral x, smul_add]⟩

/--
[IsRightIntegral.add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma IsRightIntegral.add
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [Coalgebra R H]
  {I J : H}
-- given
  (hI : IsRightIntegral R H I)
  (hJ : IsRightIntegral R H J) :
-- imply
  IsRightIntegral R H (I + J) :=
-- proof
  ⟨fun x => by rw [add_mul, hI.right_integral x, hJ.right_integral x, smul_add]⟩
end IntegralProperties
section IntegralSubmodules
variable (k : Type u) [CommSemiring k] (H : Type v) [Semiring H] [Algebra k H] [Coalgebra k H]

/--
[mem_leftIntSubmodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma mem_leftIntSubmodule
  {k : Type u}
  [CommSemiring k]
  {H : Type v}
  [Semiring H]
  [Algebra k H]
  [Coalgebra k H]
  {I : H} :
-- imply
  I ∈ leftIntSubmodule k H ↔ IsLeftIntegral k H I :=
-- proof
  Iff.rfl

/--
[mem_rightIntSubmodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma mem_rightIntSubmodule
  {k : Type u}
  [CommSemiring k]
  {H : Type v}
  [Semiring H]
  [Algebra k H]
  [Coalgebra k H]
  {I : H} :
-- imply
  I ∈ rightIntSubmodule k H ↔ IsRightIntegral k H I :=
-- proof
  Iff.rfl
end IntegralSubmodules

/--
[exists_nonzero_spanning_of_finrank_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma exists_nonzero_spanning_of_finrank_one
  {k : Type u}
  [Field k]
  {H : Type v}
  [AddCommGroup H]
  [Module k H]
  {S : Submodule k H}
-- given
  (hfr : Module.finrank k S = 1) :
-- imply
  ∃ (I₀ : H), I₀ ∈ S ∧ I₀ ≠ 0 ∧ ∀ (J : H), J ∈ S → ∃ (c : k), J = c • I₀ := by
-- proof
  haveI : FiniteDimensional k S := Module.finite_of_finrank_pos (by omega)
  haveI : Nontrivial S := by rw [← Module.finrank_pos_iff (R := k)]; omega
  obtain ⟨⟨a, ha_mem⟩, ⟨b, hb_mem⟩, hab⟩ := (inferInstance : Nontrivial S)
  by_cases ha0 : a = 0
  · subst ha0
    have hb0 : b ≠ 0 := by intro hb0; apply hab; ext; simp [hb0]
    have hspan := (finrank_eq_one_iff_of_nonzero' (K := k)
      (⟨b, hb_mem⟩ : S) (by simp [hb0])).mp hfr
    refine ⟨b, hb_mem, hb0, fun J hJ => ?_⟩
    obtain ⟨c, hc⟩ := hspan ⟨J, hJ⟩
    exact ⟨c, by simpa using (congr_arg Subtype.val hc).symm⟩
  · have hspan := (finrank_eq_one_iff_of_nonzero' (K := k)
    (⟨a, ha_mem⟩ : S) (by simp [ha0])).mp hfr
    refine ⟨a, ha_mem, ha0, fun J hJ => ?_⟩
    obtain ⟨c, hc⟩ := hspan ⟨J, hJ⟩
    exact ⟨c, by simpa using (congr_arg Subtype.val hc).symm⟩
section Prop1523
variable (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H] [Coalgebra k H]

/--
[IsLeftIntegral.sq_eq_counit_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma IsLeftIntegral.sq_eq_counit_smul
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [Coalgebra R H]
  {I : H}
-- given
  (hI : IsLeftIntegral R H I) :
-- imply
  I * I = Coalgebra.counit (R := R) I • I :=
-- proof
  hI.left_integral I

/--
[IsRightIntegral.sq_eq_counit_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma IsRightIntegral.sq_eq_counit_smul
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [Coalgebra R H]
  {I : H}
-- given
  (hI : IsRightIntegral R H I) :
-- imply
  I * I = Coalgebra.counit (R := R) I • I :=
-- proof
  hI.right_integral I

/--
[counit_ne_zero_of_sq_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma counit_ne_zero_of_sq_ne_zero
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [Coalgebra R H]
  {I : H}
-- given
  (hI : IsLeftIntegral R H I)
  (hsq : I * I ≠ 0) :
-- imply
  Coalgebra.counit (R := R) I ≠ 0 := by
-- proof
  intro hε
  exact hsq (by rw [hI.sq_eq_counit_smul, hε, zero_smul])

/--
[sq_ne_zero_of_idempotent_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma sq_ne_zero_of_idempotent_ne_zero
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [Coalgebra R H]
  {I : H}
-- given
  (hI : I * I = I)
  (hne : I ≠ 0) :
-- imply
  I * I ≠ 0 := by
-- proof
  rwa [hI]
section IntegralNormalization
variable {k : Type u} [Field k] {A : Type v} [Semiring A] [Algebra k A] [Coalgebra k A]

/--
[isLeftIntegral_normalize](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma isLeftIntegral_normalize
  {k : Type u}
  [Field k]
  {A : Type v}
  [Semiring A]
  [Algebra k A]
  [Coalgebra k A]
  {I : A}
-- given
  (hI : IsLeftIntegral k A I)
  (_hε : Coalgebra.counit (R := k) I ≠ 0) :
-- imply
  let J := (Coalgebra.counit (R := k) I)⁻¹ • I IsLeftIntegral k A J ∧ J * J = J := by
-- proof
  set c := Coalgebra.counit (R := k) I with hc_def
  refine ⟨⟨fun x => ?_⟩, ?_⟩
  ·
    show x * (c⁻¹ • I) = counit x • (c⁻¹ • I)
    rw [mul_smul_comm, hI.left_integral, smul_comm]
  ·
    show (c⁻¹ • I) * (c⁻¹ • I) = c⁻¹ • I
    rw [smul_mul_assoc, mul_smul_comm, hI.left_integral I, smul_smul, smul_smul]
    congr 1; rw [hc_def]; field_simp
end IntegralNormalization
section Prop1525_ii_implies_i
open CategoryTheory MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/--
[prop_1_52_5_ii_implies_i](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma prop_1_52_5_ii_implies_i
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {k : Type w}
  [Field k]
  [Semiring A]
  [Algebra k A]
  [Coalgebra k A]
  {I : A}
-- given
  (_hI : IsLeftIntegral k A I)
  (hε : Coalgebra.counit (R := k) I ≠ 0)
  (_hne : I ≠ 0) :
-- imply
  Coalgebra.counit (R := k) ((Coalgebra.counit (R := k) I)⁻¹ • I) = (1 : k) := by
-- proof
  simp [map_smul, inv_mul_cancel₀ hε]

/--
[prop_1_52_5_iii_iff_ii](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma prop_1_52_5_iii_iff_ii
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {k : Type u}
  [Field k]
  {H : Type v}
  [Semiring H]
  [Algebra k H]
  [Coalgebra k H]
  {I : H}
-- given
  (hI : IsLeftIntegral k H I)
  (hne : I ≠ 0) :
-- imply
  I * I ≠ 0 ↔ Coalgebra.counit (R := k) I ≠ 0 := by
-- proof
  constructor
  · exact counit_ne_zero_of_sq_ne_zero hI
  · intro hε
    rw [hI.sq_eq_counit_smul]
    exact smul_ne_zero hε hne
end Prop1525_ii_implies_i
section DistinguishedCharacter
variable (R : Type u) [CommSemiring R] (H : Type v) [Semiring H] [Algebra R H] [Coalgebra R H]

/--
[IsLeftIntegral.right_mul_isLeftIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma IsLeftIntegral.right_mul_isLeftIntegral
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [Coalgebra R H]
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Algebra R H]
  [Coalgebra R H]
  {I : H}
  {y : H}
-- given
  (hI : IsLeftIntegral R H I) :
-- imply
  IsLeftIntegral R H (I * y) :=
-- proof
  ⟨fun x => by
    rw [← mul_assoc, hI.left_integral x, smul_mul_assoc]⟩

/--
[distinguished_char_eq_counit_of_unimodular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma distinguished_char_eq_counit_of_unimodular
  {k : Type u}
  [Field k]
  {H : Type v}
  [Ring H]
  [Algebra k H]
  [Coalgebra k H]
  {I : H}
  {dc : DistinguishedCharacter k H I}
-- given
  (hI_ne : I ≠ 0)
  (huni : IsUnimodularAlgebra k H) :
-- imply
  ∀ x : H, dc.χ x = Coalgebra.counit (R := k) x := by
-- proof
  intro x
  have hIright := huni I dc.left_int
  have h1 := dc.right_law x
  have h2 := hIright.right_integral x
  have h3 : dc.χ x • I = Coalgebra.counit (R := k) x • I := h1.symm.trans h2
  by_contra h
  apply hI_ne
  have hsub : (dc.χ x - Coalgebra.counit (R := k) x) • I = 0 := by
    rwa [sub_smul, sub_eq_zero]
  obtain hab | hI_eq := smul_eq_zero.mp hsub
  · exact absurd (sub_eq_zero.mp hab) h
  · exact hI_eq

/--
[left_integral_is_right_of_char_eq_counit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma left_integral_is_right_of_char_eq_counit
  {k : Type u}
  [Field k]
  {H : Type v}
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
  ⟨fun x => by rw [dc.right_law x, hχε x]⟩
section BialgebraIntegrals
variable {R : Type u} [CommSemiring R] {H : Type v} [Semiring H] [Bialgebra R H]

/--
[IsLeftIntegral.unit_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma IsLeftIntegral.unit_mul
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Bialgebra R H]
  {I : H}
-- given
  (_hI : IsLeftIntegral R H I) :
-- imply
  (1 : H) * I = I :=
-- proof
  one_mul I

/--
[IsLeftIntegral.counit_smul_self_eq_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean)
-/
@[path]
lemma IsLeftIntegral.counit_smul_self_eq_sq
  {R : Type u}
  [CommSemiring R]
  {H : Type v}
  [Semiring H]
  [Bialgebra R H]
  {I : H}
-- given
  (hI : IsLeftIntegral R H I) :
-- imply
  Coalgebra.counit (R := R) I • I = I * I :=
-- proof
  (hI.sq_eq_counit_smul).symm
end BialgebraIntegrals
section Prop1525Full
variable {k : Type u} [Field k] {H : Type v} [Ring H] [Algebra k H] [Coalgebra k H]
/-- Equivalence (i) ↔ (ii) of Proposition 1.52.5: `H` is semisimple iff `ε(I) ≠ 0`
for a nonzero left integral `I`. -/
end Prop1525Full


-- created on 2026-10-23
