import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AlgebraicCurve.TwoChartIntegralModel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

/-- ported from external source -/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {F : Type u} [Field F] [Algebra R F]
  {j : F} [Fact (j ≠ 0)]
  {O : Type u} [CommRing O] [Algebra R O] :
-- imply
  ∃ g : Spec (CommRingCat.of (↥(chartAlgInf R F j) ⊗[R] O)) ⟶
    pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O))),
      IsOpenImmersion g ∧
      g ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R :=
  R) (A := ↥(chartAlgInf R F j)) (B := O))) ≫
    ιInf R F j ∧
        g ≫ pullback.snd _ _ =
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := ↥(chartAlgInf R F j)) (B := O)).toRingHom) ∧
        Set.range g.base = ((pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O)))) ⁻¹ᵁ ((ιInf R F j) ''ᵁ ⊤) :
          Set ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R O))))) := by
-- proof
    set A : Type u := ↥(chartAlgInf R F j) with hA
    set b : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R O)) with hb
    set a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R A)) with ha
    have hιa : ιInf R F j ≫ toBase R F j = a := ιInf_toBase R F j
    let g' : pullback a b ⟶ pullback (toBase R F j) b :=
      pullback.lift (pullback.fst a b ≫ ιInf R F j) (pullback.snd a b) (by rw [Category.assoc, hιa, pullback.condition])
    have hg'fst : g' ≫ pullback.fst _ _ = pullback.fst a b ≫ ιInf R F j := pullback.lift_fst _ _ _
    have hg'snd : g' ≫ pullback.snd _ _ = pullback.snd a b := pullback.lift_snd _ _ _
    have sq : IsPullback (pullback.fst a b) g' (ιInf R F j) (pullback.fst (toBase R F j) b) := by
      refine IsPullback.of_bot ?_ hg'fst.symm (IsPullback.of_hasPullback (toBase R F j) b)
      rw [hg'snd, hιa]
      exact IsPullback.of_hasPullback a b
    have hopen : IsOpenImmersion g' := MorphismProperty.of_isPullback sq inferInstance
    have hrange : Set.range g'.base = ((pullback.fst (toBase R F j) b) ⁻¹ᵁ ((ιInf R F j) ''ᵁ ⊤) : Set _) := by
      have e1 : g' = sq.isoPullback.hom ≫ pullback.snd (ιInf R F j) (pullback.fst (toBase R F j) b) :=
        (sq.isoPullback_hom_snd).symm
      have hs1 : Function.Surjective sq.isoPullback.hom.base := sq.isoPullback.hom.homeomorph.surjective
      rw [e1, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hs1, Set.image_univ,
        Scheme.Pullback.range_snd]
      ext x
      simp only [Set.mem_preimage, Set.mem_range]
      constructor
      ·
        rintro ⟨y, hy⟩
        exact ⟨y, trivial, hy⟩
      ·
        rintro ⟨y, -, hy⟩
        exact ⟨y, hy⟩
    refine ⟨(pullbackSpecIso R A O).inv ≫ g', inferInstance, ?_, ?_, ?_⟩
    · rw [Category.assoc, hg'fst, ← Category.assoc, pullbackSpecIso_inv_fst]
    ·
      rw [Category.assoc, hg'snd, pullbackSpecIso_inv_snd]
      rfl
    ·
      have hs2 : Function.Surjective (pullbackSpecIso R A O).inv.base := (pullbackSpecIso R A O).inv.homeomorph.surjective
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hs2, Set.image_univ, hrange]

-- created on 2026-10-23
