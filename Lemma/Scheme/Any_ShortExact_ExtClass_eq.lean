import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import Lemma.Int.P2MUtil
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry


/--
[AlgebraicGeometry_fppf_extClass_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_fppf_extClass_surjective.lean)
-/

private lemma CategoryTheory.Abelian.Ext.exists_shortExact_extClass_eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  [HasExt.{w} C]
  [EnoughInjectives C]
  {X Y : C} (e : Ext.{w} X Y 1) :
  ∃ (E : C) (f : Y ⟶ E) (g : E ⟶ X) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact), hS.extClass = e := by
  let S : ShortComplex C := ShortComplex.mk (Injective.ι Y) (cokernel.π (Injective.ι Y))
    (cokernel.condition (Injective.ι Y))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
  have he0 : e.comp (Ext.mk₀ S.f) (add_zero 1) = 0 :=
    Ext.eq_zero_of_injective (I := Injective.under Y) _
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ X hS e he0 (zero_add 1)
  let φ : X ⟶ S.X₃ := Ext.homEquiv₀ x₃
  have : Epi S.g := hS.epi_g
  have : Mono S.f := hS.mono_f
  have hpc : pullback.fst S.g φ ≫ S.g = pullback.snd S.g φ ≫ φ := pullback.condition
  let ι' : Y ⟶ pullback S.g φ := pullback.lift S.f 0 (by simp)
  have hι'fst : ι' ≫ pullback.fst S.g φ = S.f := pullback.lift_fst _ _ _
  have hι'snd : ι' ≫ pullback.snd S.g φ = 0 := pullback.lift_snd _ _ _
  have : Mono ι' := mono_of_mono_fac hι'fst
  let S' : ShortComplex C := ShortComplex.mk ι' (pullback.snd S.g φ) hι'snd
  have hS' : S'.ShortExact := by
    refine { exact := ShortComplex.exact_of_f_is_kernel _ ?_ }
    refine KernelFork.IsLimit.ofι' ι' hι'snd (fun {A} k hk =>
      ⟨hS.exact.lift (k ≫ pullback.fst S.g φ)
        (by rw [Category.assoc, hpc, reassoc_of% hk, Limits.zero_comp]), ?_⟩)
    · refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, hι'fst, ShortComplex.Exact.lift_f]
      · simp only [Category.assoc, hι'snd, Limits.comp_zero, hk]
  let ψ : S' ⟶ S :=
    { τ₁ := 𝟙 Y
      τ₂ := pullback.fst S.g φ
      τ₃ := φ
      comm₁₂ := by dsimp only [S', S]; rw [Category.id_comp, hι'fst]
      comm₂₃ := hpc }
  refine ⟨pullback S.g φ, ι', pullback.snd S.g φ, hι'snd, hS', ?_⟩
  have hnat := ShortComplex.ShortExact.extClass_naturality hS' hS ψ
  rw [show ψ.τ₁ = 𝟙 Y from rfl, Ext.comp_mk₀_id] at hnat
  rw [hnat, show ψ.τ₃ = φ from rfl, show Ext.mk₀ φ = x₃ from Ext.mk₀_homEquiv₀_apply x₃, hx₃]
@[path]
private lemma main
  {F : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}}
  {e : CategoryTheory.Abelian.Ext ((CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj (.of (ULift.{1} ℤ))) F 1} :
-- imply
  ∃ (E : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1})
    (f : F ⟶ E)
    (g : E ⟶ (CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj
      (.of (ULift.{1} ℤ)))
    (w : f ≫ g = 0)
    (hS : (CategoryTheory.ShortComplex.mk f g w).ShortExact),
    hS.extClass = e :=
-- proof
  CategoryTheory.Abelian.Ext.exists_shortExact_extClass_eq e


-- created on 2026-10-23
-- updated on 2026-10-24
