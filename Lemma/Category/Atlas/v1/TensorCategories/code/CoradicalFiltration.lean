import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part8
open Coalgebra Submodule
open scoped TensorProduct
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits


namespace Submodule

/--
[iSup_isSubcoalgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma iSup_isSubcoalgebra
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {S : ι → Submodule R C}
-- given
  (hS : ∀ i, (S i).IsSubcoalgebra) :
-- imply
  (⨆ i, S i).IsSubcoalgebra := by
-- proof
  intro a ha
  refine iSup_induction (p := S) (motive := fun x =>
    Coalgebra.comul (R := R) x ∈
      Submodule.map₂ (TensorProduct.mk R C C) (⨆ i, S i) (⨆ i, S i)) ha ?_ ?_ ?_
  · intro i x hx
    exact map₂_le_map₂ (le_iSup S i) (le_iSup S i) (hS i x hx)
  · simp [map_zero]
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy

end Submodule

/--
[coradical_isSubcoalgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma coradical_isSubcoalgebra
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C] :
-- imply
  (coradical (R := R) (C := C)).IsSubcoalgebra := by
-- proof
  unfold coradical; rw [iSup_subtype']
  exact Submodule.iSup_isSubcoalgebra (fun ⟨_, _, hSub, _⟩ => hSub)

/--
[le_coradical_of_isSimpleCoalgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma le_coradical_of_isSimpleCoalgebra
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {S : Submodule R C}
-- given
  (hS : S.IsSimpleCoalgebra) :
-- imply
  S ≤ coradical (R := R) (C := C) :=
-- proof
  le_iSup₂ (f := fun (S : Submodule R C) (_ : S.IsSimpleCoalgebra) => S) S hS

/--
[coradicalFiltration_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma coradicalFiltration_zero
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C] :
-- imply
  coradicalFiltration (R := R) (C := C) 0 = coradical :=
-- proof
  rfl

/--
[coradicalFiltration_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma coradicalFiltration_succ
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {n : ℕ} :
-- imply
  coradicalFiltration (R := R) (C := C) (n + 1) = (Submodule.map₂ (TensorProduct.mk R C C) (coradicalFiltration n) ⊤ ⊔ Submodule.map₂ (TensorProduct.mk R C C) ⊤ coradical).comap (Coalgebra.comul (R := R)) :=
-- proof
  rfl

/--
[mem_coradicalFiltration_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma mem_coradicalFiltration_succ
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {n : ℕ}
  {x : C} :
-- imply
  x ∈ coradicalFiltration (R := R) (C := C) (n + 1) ↔ Coalgebra.comul (R := R) x ∈ Submodule.map₂ (TensorProduct.mk R C C) (coradicalFiltration n) ⊤ ⊔ Submodule.map₂ (TensorProduct.mk R C C) ⊤ coradical := by
-- proof
  simp [coradicalFiltration_succ, Submodule.mem_comap]

/--
[coradicalFiltration_le_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma coradicalFiltration_le_succ
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {n : ℕ} :
-- imply
  coradicalFiltration (R := R) (C := C) n ≤ coradicalFiltration (n + 1) := by
-- proof
  cases n with
  | zero =>
    intro x hx
    simp only [coradicalFiltration]
    rwa [Submodule.mem_comap]
      (Submodule.map₂_le_map₂_right le_top (coradical_isSubcoalgebra x hx))
  | succ k =>
    apply Submodule.comap_mono
    exact sup_le_sup_right
      (Submodule.map₂_le_map₂_left (coradicalFiltration_le_succ k)) _

/--
[coradicalFiltration_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma coradicalFiltration_mono
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C] :
-- imply
  Monotone (coradicalFiltration (R := R) (C := C)) :=
-- proof
  monotone_nat_of_le_succ coradicalFiltration_le_succ

/--
[IsGrouplike.ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma IsGrouplike.ne_zero
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  [Nontrivial R]
  {g : C}
-- given
  (hg : IsGrouplike (R := R) g) :
-- imply
  g ≠ 0 := by
-- proof
  intro h
  have := hg.2
  rw [h, map_zero] at this
  exact zero_ne_one this

/--
[span_grouplike_isSubcoalgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma span_grouplike_isSubcoalgebra
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {g : C}
-- given
  (hg : Coalgebra.comul (R := R) g = g ⊗ₜ g) :
-- imply
  (Submodule.span R ({g} : Set C)).IsSubcoalgebra := by
-- proof
  intro a ha
  rw [Submodule.mem_span_singleton] at ha
  obtain ⟨r, rfl⟩ := ha
  simp only [LinearMap.map_smul, hg, TensorProduct.smul_tmul']
  exact Submodule.apply_mem_map₂ (TensorProduct.mk R C C)
    (Submodule.mem_span_singleton.mpr ⟨r, rfl⟩)
    (Submodule.mem_span_singleton.mpr ⟨1, one_smul _ _⟩)

/--
[grouplike_mem_coradical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma grouplike_mem_coradical
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {g : C}
-- given
  (_hg : IsGrouplike (R := R) g)
  (hSimple : (Submodule.span R ({g} : Set C)).IsSimpleCoalgebra) :
-- imply
  g ∈ coradical (R := R) (C := C) :=
-- proof
  le_coradical_of_isSimpleCoalgebra hSimple (Submodule.subset_span (Set.mem_singleton _))

/--
[skewPrimitive_mem_coradicalFiltration_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma skewPrimitive_mem_coradicalFiltration_one
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
-- given
  (g h x : C)
  (hg : g ∈ coradical (R := R) (C := C))
  (hh : h ∈ coradical (R := R) (C := C))
  (hx : IsSkewPrimitive (R := R) g h x) :
-- imply
  x ∈ coradicalFiltration (R := R) (C := C) 1 := by
-- proof
  simp only [coradicalFiltration]
  rw [Submodule.mem_comap]
  rw [show Coalgebra.comul (R := R) x = x ⊗ₜ g + h ⊗ₜ x from hx]
  exact Submodule.add_mem _
    (Submodule.mem_sup_right
      (Submodule.apply_mem_map₂ (TensorProduct.mk R C C) Submodule.mem_top hg))
    (Submodule.mem_sup_left
      (Submodule.apply_mem_map₂ (TensorProduct.mk R C C) hh Submodule.mem_top))

/--
[comul_coradicalFiltration_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma comul_coradicalFiltration_zero
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {x : C}
-- given
  (hx : x ∈ coradicalFiltration (R := R) (C := C) 0) :
-- imply
  Coalgebra.comul (R := R) x ∈ filtrationTensorSum (R := R) (C := C) 0 := by
-- proof
  apply Submodule.mem_iSup_of_mem (⟨0, Nat.zero_lt_one⟩ : Fin 1)
  simp only [coradicalFiltration]
  exact coradical_isSubcoalgebra x hx

/--
[pointed_simple_generator_grouplike](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma pointed_simple_generator_grouplike
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {R : Type u}
  {C : Type v}
  [Field R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {S : Submodule R C}
  {g : C}
-- given
  (hS : S.IsSimpleCoalgebra)
  (hg_span : S = Submodule.span R {g}) :
-- imply
  ∃ g' : C, g' ∈ grouplikes (R := R) (C := C) ∧ S = Submodule.span R {g'} := by
-- proof
  have hg_mem : g ∈ S := hg_span ▸ Submodule.subset_span (Set.mem_singleton _)
  have hcomul_mem := hS.2.1 g hg_mem
  have hSS : Submodule.map₂ (TensorProduct.mk R C C) S S =
    Submodule.span R {g ⊗ₜ[R] g} := by
    rw [hg_span, Submodule.map₂_span_span]; simp
  rw [hSS, Submodule.mem_span_singleton] at hcomul_mem
  obtain ⟨c, hc⟩ := hcomul_mem
  have hcomul : Coalgebra.comul (R := R) g = c • (g ⊗ₜ[R] g) := hc.symm
  have hg_ne : g ≠ 0 := by
    intro h; apply hS.1; rw [hg_span, h]; exact Submodule.span_singleton_eq_bot.mpr rfl
  set eg := Coalgebra.counit (R := R) g with heg_def
  have hc_eg : c * eg = 1 := by
    have hax := Coalgebra.rTensor_counit_comp_comul (R := R) (A := C)
    have heval : LinearMap.rTensor C (Coalgebra.counit (R := R))
      (Coalgebra.comul (R := R) g) =
      (TensorProduct.mk R R C) 1 g := congr_fun (congr_arg DFunLike.coe hax) g
    rw [hcomul, LinearMap.map_smul, LinearMap.rTensor_tmul] at heval
    have := congr_arg (TensorProduct.lid R C) heval
    simp only [TensorProduct.lid_tmul, map_smul, smul_smul, TensorProduct.mk_apply] at this
    have h1 : (c * eg - 1) • g = 0 := by rw [sub_smul, this, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hg_ne)
  have heg_ne : eg ≠ 0 := right_ne_zero_of_mul (by rw [hc_eg]; exact one_ne_zero)
  have hc_eq : c = eg⁻¹ := by
    rw [show c = c * 1 from (mul_one c).symm, ← mul_inv_cancel₀ heg_ne,
      ← mul_assoc, hc_eg, one_mul]
  refine ⟨eg⁻¹ • g, ⟨?_, ?_⟩, ?_⟩
  ·
    rw [LinearMap.map_smul, hcomul, smul_smul, hc_eq]
    conv_rhs => rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']
    rw [smul_smul, mul_comm]
  ·
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ heg_ne]
  ·
    rw [hg_span]
    exact (Submodule.span_singleton_smul_eq (IsUnit.mk0 eg⁻¹ (inv_ne_zero heg_ne)) g).symm

/--
[span_grouplike_simple_in_pointed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma span_grouplike_simple_in_pointed
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {R : Type u}
  {C : Type v}
  [Field R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C] :
-- imply
  IsPointedCoalgebra (R := R) (C := C) → ∀ (g : C), g ∈ grouplikes (R := R) (C := C) → (Submodule.span R ({g} : Set C)).IsSimpleCoalgebra := by
-- proof
  intro _ g hg
  refine ⟨?_, span_grouplike_isSubcoalgebra g hg.1, ?_⟩
  ·
    intro h
    have hg_ne : g ≠ 0 := by
      intro hg0; have := hg.2; rw [hg0, map_zero] at this; exact zero_ne_one this
    exact hg_ne (Submodule.span_singleton_eq_bot.mp h)
  ·
    intro T _hT_sub hT_le
    by_cases hT_ne : T = ⊥
    · exact Or.inl hT_ne
    · right
      obtain ⟨t_val, t_mem, t_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT_ne
      have ht_span : t_val ∈ Submodule.span R ({g} : Set C) := hT_le t_mem
      rw [Submodule.mem_span_singleton] at ht_span
      obtain ⟨r, hr⟩ := ht_span
      have hr_ne : r ≠ 0 := by
        intro hr0; rw [hr0, zero_smul] at hr; exact t_ne hr.symm
      have hg_in_T : g ∈ T := by
        have : g = r⁻¹ • t_val := by rw [← hr, smul_smul, inv_mul_cancel₀ hr_ne, one_smul]
        rw [this]; exact T.smul_mem _ t_mem
      exact le_antisymm hT_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hg_in_T))

/--
[iSupIndep_of_projections](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma iSupIndep_of_projections
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  [CommRing R']
  [AddCommGroup M]
  [Module R' M]
  {t : ι → Submodule R' M}
  {π : ι → (M →ₗ[R'] M)}
-- given
  (hProject : ∀ i, ∀ x ∈ t i, π i x = x)
  (hOrth : ∀ i j, i ≠ j → ∀ x ∈ t j, π i x = 0) :
-- imply
  iSupIndep t := by
-- proof
  rw [iSupIndep_def]
  intro i
  rw [disjoint_iff]
  ext x
  simp only [Submodule.mem_inf, Submodule.mem_bot]
  constructor
  · rintro ⟨hxi, hxS⟩
    have h1 : (π i) x = x := hProject i x hxi
    have h2 : (π i) x = 0 := by
      have hker : (⨆ j, ⨆ (_ : j ≠ i), t j) ≤ LinearMap.ker (π i) := by
        apply iSup_le; intro j
        apply iSup_le; intro hji z hz
        simp only [LinearMap.mem_ker]
        exact hOrth i j (Ne.symm hji) z hz
      exact LinearMap.mem_ker.mp (hker hxS)
    rw [← h1, h2]
  · rintro rfl
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩

/--
[coalgebraRightSlice_skewPrim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma coalgebraRightSlice_skewPrim
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {f : C →ₗ[R] R}
  {x g h : C}
-- given
  (hskew : Coalgebra.comul (R := R) x = x ⊗ₜ g + h ⊗ₜ x) :
-- imply
  coalgebraRightSlice (R := R) f x = f g • x + f x • h := by
-- proof
  simp only [coalgebraRightSlice, LinearMap.comp_apply, hskew, map_add,
    LinearMap.lTensor_tmul]
  simp [TensorProduct.rid_tmul]

/--
[coalgebraLeftSlice_skewPrim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma coalgebraLeftSlice_skewPrim
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {f : C →ₗ[R] R}
  {x g h : C}
-- given
  (hskew : Coalgebra.comul (R := R) x = x ⊗ₜ g + h ⊗ₜ x) :
-- imply
  coalgebraLeftSlice (R := R) f x = f x • g + f h • x := by
-- proof
  simp only [coalgebraLeftSlice, LinearMap.comp_apply, hskew, map_add,
    LinearMap.rTensor_tmul]
  simp [TensorProduct.lid_tmul]

/--
[coalgebraLeftSlice_grouplike](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma coalgebraLeftSlice_grouplike
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {f : C →ₗ[R] R}
  {g : C}
-- given
  (hgl : Coalgebra.comul (R := R) g = g ⊗ₜ g) :
-- imply
  coalgebraLeftSlice (R := R) f g = f g • g := by
-- proof
  simp only [coalgebraLeftSlice, LinearMap.comp_apply, hgl,
    LinearMap.rTensor_tmul]
  simp [TensorProduct.lid_tmul]

/--
[grouplike_mem_coradical_pointed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma grouplike_mem_coradical_pointed
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {R : Type u}
  {C : Type v}
  [Field R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {g : C}
-- given
  (hPointed : IsPointedCoalgebra (R := R) (C := C))
  (hg : g ∈ grouplikes (R := R) (C := C)) :
-- imply
  g ∈ coradical (R := R) (C := C) :=
-- proof
  le_coradical_of_isSimpleCoalgebra
    (span_grouplike_simple_in_pointed R C hPointed g hg)
    (Submodule.subset_span (Set.mem_singleton _))

/--
[taftWilson_coradical_eq_span_grouplikes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma taftWilson_coradical_eq_span_grouplikes
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {R : Type u}
  {C : Type v}
  [Field R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
-- given
  (hPointed : IsPointedCoalgebra (R := R) (C := C)) :
-- imply
  coradical (R := R) (C := C) = ⨆ (g : C) (_ : g ∈ grouplikes (R := R) (C := C)), Submodule.span R {g} := by
-- proof
  apply le_antisymm
  ·
    apply iSup₂_le
    intro S hS
    obtain ⟨g, hg_span⟩ := hPointed S hS
    obtain ⟨g', hg'_gl, hg'_span⟩ := pointed_simple_generator_grouplike R C S hS g hg_span
    rw [hg'_span]
    exact le_iSup₂ (f := fun (g : C) (_ : g ∈ grouplikes (R := R) (C := C)) =>
      Submodule.span R {g}) g' hg'_gl
  ·
    apply iSup₂_le
    intro g hg
    exact le_coradical_of_isSimpleCoalgebra
      (span_grouplike_simple_in_pointed R C hPointed g hg)

/--
[Coalgebra.sum_smul_counit_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma Coalgebra.sum_smul_counit_right
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  [CommRing R]
  [AddCommGroup A]
  [Module R A]
  [Coalgebra R A]
  {a : A}
  {repr : Coalgebra.Repr R a} :
-- imply
  ∑ x ∈ repr.index, Coalgebra.counit (R := R) (repr.right x) • repr.left x = a := by
-- proof
  have h := Coalgebra.sum_tmul_counit_eq repr
  have h2 : TensorProduct.lift ((LinearMap.lsmul R A).flip)
    (∑ i ∈ repr.index, repr.left i ⊗ₜ[R] Coalgebra.counit (R := R) (repr.right i))
    = TensorProduct.lift ((LinearMap.lsmul R A).flip) (a ⊗ₜ[R] (1 : R)) := by rw [h]
  simp only [map_sum, TensorProduct.lift.tmul, LinearMap.flip_apply, LinearMap.lsmul_apply,
    one_smul] at h2
  exact h2

/--
[coradicalFiltration_eq_of_C0_eq_C1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma coradicalFiltration_eq_of_C0_eq_C1
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  {n : ℕ}
-- given
  (h : coradicalFiltration (R := R) (C := C) 0 = coradicalFiltration 1) :
-- imply
  coradicalFiltration (R := R) (C := C) n = coradicalFiltration 0 := by
-- proof
  induction n with
  | zero => rfl
  | succ k ih =>
    show coradicalFiltration (k + 1) = coradicalFiltration 0
    conv_lhs => simp only [coradicalFiltration]
    rwa [ih]

/--
[ideal_pow_mem_of_sub_mem_higher](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma ideal_pow_mem_of_sub_mem_higher
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  [CommRing B]
  {I : Ideal B}
  {y z : B}
  {n : ℕ}
-- given
  (hy : y ∈ I ^ n)
  (hz : y - z ∈ I ^ (n + 1)) :
-- imply
  z ∈ I ^ n := by
-- proof
  rw [show z = y - (y - z) from by ring]
  exact (I ^ n).sub_mem hy (Ideal.pow_le_pow_right (by omega) hz)

/--
[lift_from_ideal_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma lift_from_ideal_pow
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  [CommRing A]
  [CommRing B]
  {f : A →+* B}
  {I : Ideal B}
-- given
  (hsurj : ∀ b : B, ∃ a : A, b - f a ∈ I ^ 2) :
-- imply
  ∀ n : ℕ, ∀ c ∈ I ^ (n + 1), ∃ a : A, c - f a ∈ I ^ (n + 2) := by
-- proof
  intro n
  induction n with
  | zero => intro c _; exact hsurj c
  | succ k ih =>
    intro c hc
    rw [show k + 1 + 1 = k + 2 from by omega] at hc
    rw [pow_succ'] at hc
    refine Submodule.mul_induction_on hc ?_ ?_
    ·
      intro x hx y hy
      obtain ⟨α, hα⟩ := hsurj x
      obtain ⟨β, hβ⟩ := ih y hy
      refine ⟨α * β, ?_⟩
      rw [map_mul, show x * y - f α * f β = x * (y - f β) + (x - f α) * f β from by ring,
        show k + 1 + 2 = 1 + (k + 2) from by omega]
      exact (I ^ (1 + (k + 2))).add_mem
        (by rw [pow_add, pow_one]; exact Ideal.mul_mem_mul hx hβ)
        (by rw [show 1 + (k + 2) = 2 + (k + 1) from by omega, pow_add]
          exact Ideal.mul_mem_mul hα (ideal_pow_mem_of_sub_mem_higher hy hβ))
    ·
      intro x y ⟨ax, hax⟩ ⟨ay, hay⟩
      exact ⟨ax + ay, by
        rw [map_add, show x + y - (f ax + f ay) = (x - f ax) + (y - f ay) from by ring]
        exact (I ^ (k + 1 + 2)).add_mem hax hay⟩

/--
[algebra_hom_surjective_of_surjective_mod_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma algebra_hom_surjective_of_surjective_mod_sq
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  [CommRing A]
  [CommRing B]
  {f : A →+* B}
  {I : Ideal B}
-- given
  (hnil : ∃ N : ℕ, I ^ N = ⊥)
  (hsurj : ∀ b : B, ∃ a : A, b - f a ∈ I ^ 2) :
-- imply
  Function.Surjective f := by
-- proof
  obtain ⟨N, hN⟩ := hnil
  intro b
  suffices h : ∀ k : ℕ, ∃ a : A, b - f a ∈ I ^ (k + 2) by
    obtain ⟨a, ha⟩ := h N
    refine ⟨a, ?_⟩
    have : I ^ (N + 2) = ⊥ := le_bot_iff.mp
      ((Ideal.pow_le_pow_right (by omega : N ≤ N + 2)).trans (le_of_eq hN))
    rw [this, Ideal.mem_bot] at ha
    exact (sub_eq_zero.mp ha).symm
  intro k
  induction k with
  | zero => exact hsurj b
  | succ m ihm =>
    obtain ⟨a₀, ha₀⟩ := ihm
    obtain ⟨a₁, ha₁⟩ := lift_from_ideal_pow f I hsurj (m + 1) (b - f a₀)
      (by rwa [show m + 1 + 1 = m + 2 from by omega])
    refine ⟨a₀ + a₁, ?_⟩
    rw [map_add, show b - (f a₀ + f a₁) = (b - f a₀) - f a₁ from by ring,
      show m + 1 + 2 = m + 1 + 2 from rfl]
    exact ha₁

/--
[ext1_subsingleton_of_ses_cov](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma ext1_subsingleton_of_ses_cov
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  [CategoryTheory.Category 𝒞]
  [CategoryTheory.Abelian 𝒞]
  {X : 𝒞}
  {S : ShortComplex 𝒞}
-- given
  (hS : S.ShortExact)
  (h0 : Subsingleton (Ext X S.X₁ 1))
  (h2 : Subsingleton (Ext X S.X₃ 1)) :
-- imply
  Subsingleton (Ext X S.X₂ 1) := by
-- proof
  constructor; intro a b
  have ha : a.comp (Ext.mk₀ S.g) (add_zero 1) = 0 := h3.elim _ _
  have hb : b.comp (Ext.mk₀ S.g) (add_zero 1) = 0 := h3.elim _ _
  obtain ⟨a₁, ha₁⟩ := Ext.covariant_sequence_exact₂ X hS a ha
  obtain ⟨b₁, hb₁⟩ := Ext.covariant_sequence_exact₂ X hS b hb
  rw [← ha₁, ← hb₁, h1.elim a₁ b₁]

/--
[ext1_subsingleton_of_ses_contra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma ext1_subsingleton_of_ses_contra
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  [CategoryTheory.Category 𝒞]
  [CategoryTheory.Abelian 𝒞]
  {Y : 𝒞}
  {S : ShortComplex 𝒞}
-- given
  (hS : S.ShortExact)
  (h0 : Subsingleton (Ext S.X₁ Y 1))
  (h2 : Subsingleton (Ext S.X₃ Y 1)) :
-- imply
  Subsingleton (Ext S.X₂ Y 1) := by
-- proof
  constructor; intro a b
  have ha : (Ext.mk₀ S.f).comp a (zero_add 1) = 0 := h1.elim _ _
  have hb : (Ext.mk₀ S.f).comp b (zero_add 1) = 0 := h1.elim _ _
  obtain ⟨a₃, ha₃⟩ := Ext.contravariant_sequence_exact₂ hS Y a ha
  obtain ⟨b₃, hb₃⟩ := Ext.contravariant_sequence_exact₂ hS Y b hb
  rw [← ha₃, ← hb₃, h3.elim a₃ b₃]

/--
[ext1_subsingleton_of_simple_source](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma ext1_subsingleton_of_simple_source
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  [CategoryTheory.Category 𝒞]
  [CategoryTheory.Abelian 𝒞]
  [hLF : IsLocallyFiniteLength 𝒞]
  {X : 𝒞}
  [hX : Simple X]
  {Y : 𝒞}
-- given
  (hvan : ∀ (X Y : 𝒞) [Simple X] [Simple Y], Subsingleton (Ext X Y 1)) :
-- imply
  Subsingleton (Ext X Y 1) := by
-- proof
  suffices ∀ (n : ℕ) (Y : 𝒞), hLF.length Y = n → Subsingleton (Ext X Y 1) from
    this (hLF.length Y) Y rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro Y hY
    by_cases hYz : IsZero Y
    · haveI : Injective Y := hYz.injective
      exact subsingleton_of_forall_eq 0 (fun e => Ext.eq_zero_of_injective e)
    by_cases hYs : Simple Y
    · exact hvan X Y
    · obtain ⟨S, hSE, hS2, hS3, hlen⟩ :=
      IsLocallyFiniteLength.exists_ses_simple_quotient Y hYz hYs
      subst hS2
      exact ext1_subsingleton_of_ses_cov hSE
        (ih (hLF.length S.X₁) (by omega) S.X₁ rfl)
        (by haveI := hS3; exact hvan X S.X₃)

/--
[ext1_vanishes_for_simples_implies_semisimple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma ext1_vanishes_for_simples_implies_semisimple
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  [CategoryTheory.Category 𝒞]
  [CategoryTheory.Abelian 𝒞]
  {𝒞 : Type*}
  [CategoryTheory.Category 𝒞]
  [CategoryTheory.Abelian 𝒞]
  [CategoryTheory.HasExt 𝒞]
  [hLF : IsLocallyFiniteLength 𝒞] :
-- imply
  Ext1VanishesForSimples 𝒞 → IsSemisimpleCat 𝒞 := by
-- proof
  intro hvan X Y
  suffices ∀ (n : ℕ) (X : 𝒞), hLF.length X = n → Subsingleton (Ext X Y 1) from
    this (hLF.length X) X rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro X hX
    by_cases hXz : IsZero X
    · haveI : Projective X := hXz.projective
      exact subsingleton_of_forall_eq 0 (fun e => Ext.eq_zero_of_projective e)
    by_cases hXs : Simple X
    · haveI := hXs
      exact ext1_subsingleton_of_simple_source (fun X Y => hvan X Y) X Y
    · obtain ⟨S, hSE, hS2, hS3, hlen⟩ :=
      IsLocallyFiniteLength.exists_ses_simple_quotient X hXz hXs
      subst hS2
      exact ext1_subsingleton_of_ses_contra hSE
        (ih (hLF.length S.X₁) (by omega) S.X₁ rfl)
        (by haveI := hS3
          exact ext1_subsingleton_of_simple_source (fun X Y => hvan X Y) S.X₃ Y)

/--
[tensor_submodule_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma tensor_submodule_mul_le
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  [CommRing R]
  [Ring H]
  [HopfAlgebra R H]
  {M₁ M₂ N₁ N₂ : Submodule R H} :
-- imply
  Submodule.map₂ (TensorProduct.mk R H H) M₁ N₁ * Submodule.map₂ (TensorProduct.mk R H H) M₂ N₂ ≤ Submodule.map₂ (TensorProduct.mk R H H) (M₁ * M₂) (N₁ * N₂) := by
-- proof
  rw [Submodule.mul_le]
  intro x hx y hy
  suffices h : ∀ m₁ ∈ M₁, ∀ n₁ ∈ N₁, (m₁ ⊗ₜ[R] n₁) * y ∈
    Submodule.map₂ (TensorProduct.mk R H H) (M₁ * M₂) (N₁ * N₂) by
    have : Submodule.map₂ (TensorProduct.mk R H H) M₁ N₁ ≤
      (Submodule.map₂ (TensorProduct.mk R H H) (M₁ * M₂) (N₁ * N₂)).comap
        (LinearMap.mulRight R y) := by
      rw [Submodule.map₂_le]
      intro m₁ hm₁ n₁ hn₁
      simp only [Submodule.mem_comap, LinearMap.mulRight_apply]
      exact h m₁ hm₁ n₁ hn₁
    exact this hx
  intro m₁ hm₁ n₁ hn₁
  suffices h₂ : ∀ m₂ ∈ M₂, ∀ n₂ ∈ N₂, (m₁ ⊗ₜ[R] n₁) * (m₂ ⊗ₜ[R] n₂) ∈
    Submodule.map₂ (TensorProduct.mk R H H) (M₁ * M₂) (N₁ * N₂) by
    have : Submodule.map₂ (TensorProduct.mk R H H) M₂ N₂ ≤
      (Submodule.map₂ (TensorProduct.mk R H H) (M₁ * M₂) (N₁ * N₂)).comap
        (LinearMap.mulLeft R (m₁ ⊗ₜ n₁)) := by
      rw [Submodule.map₂_le]
      intro m₂ hm₂ n₂ hn₂
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
      exact h₂ m₂ hm₂ n₂ hn₂
    exact this hy
  intro m₂ hm₂ n₂ hn₂
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  exact Submodule.apply_mem_map₂ _ (Submodule.mul_mem_mul hm₁ hm₂)
    (Submodule.mul_mem_mul hn₁ hn₂)

/--
[mul_grouplikes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma mul_grouplikes
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  [CommRing R]
  [Ring H]
  [HopfAlgebra R H]
-- given
  (g h : H)
  (hg : g ∈ grouplikes (R := R) (C := H))
  (hh : h ∈ grouplikes (R := R) (C := H)) :
-- imply
  g * h ∈ grouplikes (R := R) (C := H) := by
-- proof
  constructor
  · rw [Bialgebra.comul_mul, hg.1, hh.1, Algebra.TensorProduct.tmul_mul_tmul]
  · rw [Bialgebra.counit_mul, hg.2, hh.2, one_mul]

/--
[coradical_mul_self_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean)
-/
@[path]
lemma coradical_mul_self_le
  {R : Type u}
  {C : Type v}
  [CommRing R]
  [AddCommGroup C]
  [Module R C]
  [Coalgebra R C]
  [Field R]
  [Ring H]
  [HopfAlgebra R H]
-- given
  (hpt : IsPointedCoalgebra (R := R) (C := H)) :
-- imply
  coradicalFiltration (R := R) (C := H) 0 * coradicalFiltration 0 ≤ coradicalFiltration 0 := by
-- proof
  simp only [coradicalFiltration_zero]
  rw [Submodule.mul_le]
  intro x hx y hy
  have h_eq := taftWilson_coradical_eq_span_grouplikes R H hpt
  rw [h_eq] at hx hy ⊢
  rw [iSup_subtype'] at hx hy ⊢
  refine Submodule.iSup_induction (motive := fun x => x * y ∈ ⨆ (g : {g // g ∈ grouplikes (R := R) (C := H)}), Submodule.span R {(g : H)})
    (fun (g : {g // g ∈ grouplikes (R := R) (C := H)}) => Submodule.span R {(g : H)})
    hx (fun g x hx_span => ?_) ?_ (fun x₁ x₂ hx₁ hx₂ => ?_)
  ·
    refine Submodule.iSup_induction (motive := fun y => x * y ∈ ⨆ (g : {g // g ∈ grouplikes (R := R) (C := H)}), Submodule.span R {(g : H)})
      (fun (g' : {g // g ∈ grouplikes (R := R) (C := H)}) => Submodule.span R {(g' : H)})
      hy (fun g' y hy_span => ?_) ?_ (fun y₁ y₂ hy₁ hy₂ => ?_)
    ·
      rw [Submodule.mem_span_singleton] at hx_span hy_span
      obtain ⟨r₁, rfl⟩ := hx_span
      obtain ⟨r₂, rfl⟩ := hy_span
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
      have hgg' : (g : H) * (g' : H) ∈ grouplikes (R := R) (C := H) :=
        mul_grouplikes _ _ g.2 g'.2
      exact (⨆ (g : {g // g ∈ grouplikes (R := R) (C := H)}), Submodule.span R {(g : H)}).smul_mem _
        ((⨆ (g : {g // g ∈ grouplikes (R := R) (C := H)}), Submodule.span R {(g : H)}).smul_mem _
          (Submodule.mem_iSup_of_mem ⟨_, hgg'⟩
            (Submodule.subset_span (Set.mem_singleton _))))
    ·
      show x * 0 ∈ _
      rw [mul_zero]
      exact (⨆ (g : {g // g ∈ grouplikes (R := R) (C := H)}), Submodule.span R {(g : H)}).zero_mem
    ·
      show x * (y₁ + y₂) ∈ _
      rw [mul_add]
      exact (⨆ (g : {g // g ∈ grouplikes (R := R) (C := H)}), Submodule.span R {(g : H)}).add_mem hy₁ hy₂
  ·
    show 0 * y ∈ _
    rw [zero_mul]
    exact (⨆ (g : {g // g ∈ grouplikes (R := R) (C := H)}), Submodule.span R {(g : H)}).zero_mem
  ·
    show (x₁ + x₂) * y ∈ _
    rw [add_mul]
    exact (⨆ (g : {g // g ∈ grouplikes (R := R) (C := H)}), Submodule.span R {(g : H)}).add_mem hx₁ hx₂


-- created on 2026-10-23
