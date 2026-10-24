import Mathlib
import Lemma.Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Lemma.Definitions.Def_ModularCurve_IgusaScheme
import Lemma.Definitions.Def_AlgebraicCurve_CurveModel
import Lemma.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Lemma.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Lemma.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Lemma.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Lemma.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Lemma.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Lemma.Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing AlgebraicGeometry.RelPicard

noncomputable section

namespace ModularCurve.JZeroNeronObjectAtP

structure LevelModel (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) where

  ρ : baseRing p →+* ↥A

  hρ : A.subtype.comp ρ = algebraMap (baseRing p) (AlgebraicClosure ℚ)

  [proper₀ : IsProper (IgusaScheme.igusaTo N₀ p)]

  φinf : ↥(IgusaScheme.chartAlgInf N₀ p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(GaloisRep.ratLocalizedAt p)
  φinf_spec : ∀ x : ↥(IgusaScheme.chartAlgInf N₀ p),
    ((φinf x : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) =
      ((x : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ).coeff 0

  ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) (IgusaScheme.igusaTo N₀ p)

  ε₀_chart : ε₀.1 = Spec.map (CommRingCat.ofHom φinf.toRingHom) ≫ IgusaScheme.ιInf N₀ p

  D₀ : RelativePic0Designation (baseRing p) (IgusaScheme.igusaTo N₀ p)

  rep : RepresentsRelSubPic (IgusaScheme.igusaTo N₀ p) ε₀ (algEquivZeroCut (IgusaScheme.igusaTo N₀ p) ε₀) D₀

  aj₀ : SchemeHomOver (IgusaScheme.igusaTo N₀ p) D₀.toBase

  haj₀ε : ε₀.1 ≫ aj₀.1 = D₀.zeroSection

  haj₀ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ base p)
      (x : SchemeHomOver t (IgusaScheme.igusaTo N₀ p)),
    Nonempty ((rep.poincare.pullbackAlong
        ⟨x.1 ≫ aj₀.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj₀.2).trans x.2)⟩).L ≅
      (RelEffCartierDiv.ofPoint (IgusaScheme.igusaTo N₀ p) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (IgusaScheme.igusaTo N₀ p) (t ≫ ε₀.1)
          ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε₀.2).trans (Category.comp_id t)))).idealModule)

  pts : JZero N₀ ≃ SchemeHomOver (genPt p) D₀.toBase

  ptsSp : JZeroC (ResidueField ↥A) N₀ ≃ SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D₀.toBase

  Meta₀ : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N₀)
  eeta₀ : Meta₀.C ⟶ pullback (IgusaScheme.igusaTo N₀ p) (genPt p)
  [eeta₀_iso : IsIso eeta₀]
  heeta₀ : eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase

  [Meta₀_chart_nonempty : Nonempty (Scheme.Opens.toScheme
      ((eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ p) ''ᵁ ⊤)))]

  Meta₀_pin : ∀ a : ↥(IgusaScheme.chartAlgFin N₀ p),
    ((Meta₀.ffEquiv.symm
        (Meta₀.C.germToFunctionField
          ((eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p)) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ p) ''ᵁ ⊤))
          (((eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p)).app ((IgusaScheme.ιFin N₀ p) ''ᵁ ⊤)).hom
            (((IgusaScheme.ιFin N₀ p).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ p))).inv a))))
        : ↥(modularFunctionFieldBar N₀)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ)

  pts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
    s.1 ≫ eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) = genPt p ≫ ε₀.1 →
    ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N₀),
      (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N₀)) =
        Finsupp.single (Meta₀.pointEquivPlace x) 1 - Finsupp.single (Meta₀.pointEquivPlace s) 1 ∧
      (pts (Pic0.mk Dv)).1 = x.1 ≫ eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) ≫ aj₀.1

namespace LevelModel

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}

attribute [instance] LevelModel.eeta₀_iso LevelModel.Meta₀_chart_nonempty

abbrev σA (M : LevelModel N₀ p A) : Spec (CommRingCat.of ↥A) ⟶ base p := Spec.map (CommRingCat.ofHom M.ρ)

abbrev toκ (M : LevelModel N₀ p A) : baseRing p →+* ResidueField ↥A := (residue ↥A).comp M.ρ

theorem barPt_σA (M : LevelModel N₀ p A) : barPt A ≫ M.σA = genPt p := by
  simp only [barPt, genPt, σA, ← Spec.map_comp, ← CommRingCat.ofHom_comp, M.hρ]

abbrev law (M : LevelModel N₀ p A) : RelativeGroupLaw (baseRing p) M.D₀.toBase :=
  RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (IgusaScheme.igusaTo N₀ p) M.ε₀) M.rep

def toLevelData (M : LevelModel N₀ p A) : LevelData N₀ p A where
  σA := M.σA
  hσA := M.barPt_σA
  X := M.D₀.P
  f := M.D₀.toBase
  L := M.law
  pts := M.pts
  ptsSp := M.ptsSp

end LevelModel

end ModularCurve.JZeroNeronObjectAtP

end
