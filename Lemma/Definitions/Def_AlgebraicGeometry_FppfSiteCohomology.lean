import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

instance : MorphismProperty.IsMultiplicative @LocallyOfFinitePresentation where
  id_mem _ := inferInstance

abbrev fppfProperty : MorphismProperty Scheme.{u} := @Flat ⊓ @LocallyOfFinitePresentation

example : fppfProperty.{u}.IsStableUnderBaseChange := inferInstance
example : fppfProperty.{u}.IsMultiplicative := inferInstance
example : fppfProperty.{u}.IsStableUnderComposition := inferInstance
example : fppfProperty.{u}.RespectsIso := inferInstance
example : fppfProperty.{u}.ContainsIdentities := inferInstance
example : fppfProperty.{u}.HasPullbacks := inferInstance

theorem fppfPrecoverage_eq_precoverage_fppfProperty :
    fppfPrecoverage.{u} = Scheme.precoverage fppfProperty := rfl

instance : fppfPrecoverage.{u}.HasIsos :=
  inferInstanceAs (Scheme.precoverage fppfProperty.{u}).HasIsos

instance : fppfPrecoverage.{u}.HasPullbacks :=
  inferInstanceAs (Scheme.precoverage fppfProperty.{u}).HasPullbacks

def fppfPretopology : Pretopology Scheme.{u} := Scheme.pretopology fppfProperty

theorem fppfTopology_eq_grothendieckTopology :
    fppfTopology.{u} = Scheme.grothendieckTopology fppfProperty := rfl

theorem fppfTopology_eq_toGrothendieck_fppfPretopology :
    fppfTopology.{u} = fppfPretopology.toGrothendieck :=
  Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck.symm

theorem etale_le_fppfProperty : @Etale ≤ fppfProperty.{u} := by
  intro X Y f hf
  have h := Etale.iff_flat_and_formallyUnramified.mp hf
  exact ⟨h.1, h.2.2⟩

theorem etalePrecoverage_le_fppfPrecoverage : etalePrecoverage.{u} ≤ fppfPrecoverage :=
  Scheme.precoverage_mono etale_le_fppfProperty

theorem etaleTopology_le_fppfTopology : etaleTopology.{u} ≤ fppfTopology :=
  Precoverage.toGrothendieck_mono etalePrecoverage_le_fppfPrecoverage

theorem zariskiTopology_le_fppfTopology : zariskiTopology.{u} ≤ fppfTopology :=
  Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fppfPrecoverage

example : fppfTopology.{u}.Subcanonical := inferInstance

protected def Fppf (S : Scheme.{u}) : Type (u + 1) := MorphismProperty.Over fppfProperty ⊤ S

instance (S : Scheme.{u}) : Category.{u} S.Fppf :=
  inferInstanceAs <| Category.{u} (MorphismProperty.Over fppfProperty ⊤ S)

namespace Fppf

variable (S : Scheme.{u})

instance (U : S.Fppf) : Flat U.hom := U.prop.1
instance (U : S.Fppf) : LocallyOfFinitePresentation U.hom := U.prop.2

variable {S} in

protected noncomputable def mk {X : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] : S.Fppf :=
  MorphismProperty.Over.mk ⊤ f ⟨‹_›, ‹_›⟩

protected def forget : S.Fppf ⥤ Over S := MorphismProperty.Over.forget fppfProperty ⊤ S

instance : (Fppf.forget S).Full :=
  inferInstanceAs (MorphismProperty.Over.forget _ _ _).Full

instance : (Fppf.forget S).Faithful :=
  inferInstanceAs (MorphismProperty.Over.forget _ _ _).Faithful

end Fppf

def smallFppfTopology (S : Scheme.{u}) : GrothendieckTopology S.Fppf :=
  S.smallGrothendieckTopology (P := fppfProperty)

theorem overGrothendieckTopology_fppfProperty_eq (S : Scheme.{u}) :
    S.overGrothendieckTopology fppfProperty = fppfTopology.over S := rfl

instance (S : Scheme.{u}) :
    (Fppf.forget S).LocallyCoverDense (fppfTopology.over S) :=
  inferInstanceAs <|
    (MorphismProperty.Over.forget fppfProperty ⊤ S).LocallyCoverDense
      (S.overGrothendieckTopology fppfProperty)

theorem smallFppfTopology_eq_restrictedTopology (S : Scheme.{u}) :
    smallFppfTopology S = (Fppf.forget S).restrictedTopology (fppfTopology.over S) := rfl

instance (S : Scheme.{u}) :
    (Fppf.forget S).IsCocontinuous (smallFppfTopology S) (fppfTopology.over S) :=
  inferInstanceAs <|
    (MorphismProperty.Over.forget fppfProperty ⊤ S).IsCocontinuous
      ((MorphismProperty.Over.forget fppfProperty ⊤ S).restrictedTopology
        (S.overGrothendieckTopology fppfProperty))
      (S.overGrothendieckTopology fppfProperty)

example (S : Scheme.{u}) : EssentiallySmall.{u + 1} S.Fppf := inferInstance

noncomputable def fppfTerminal (S : Scheme.{u}) : S.Fppf :=
  MorphismProperty.Over.mk ⊤ (𝟙 S) (fppfProperty.id_mem S)

noncomputable def fppfTerminalIsTerminal (S : Scheme.{u}) : IsTerminal (fppfTerminal S) :=
  MorphismProperty.Over.mkIdTerminal fppfProperty S

instance (S : Scheme.{u}) : HasTerminal S.Fppf :=
  (fppfTerminalIsTerminal S).hasTerminal

variable (S : Scheme.{u})

instance hasSheafify_smallFppfTopology : HasSheafify (smallFppfTopology S) Ab.{u + 1} :=
  inferInstance

noncomputable instance abelian_sheaf_smallFppfTopology :
    Abelian (Sheaf (smallFppfTopology S) Ab.{u + 1}) :=
  inferInstance

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in

instance isGrothendieckAbelian_sheaf_smallFppfTopology :
    IsGrothendieckAbelian.{u + 1} (Sheaf (smallFppfTopology S) Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} S.Fppf := inferInstance
  exact IsGrothendieckAbelian.of_equivalence
    ((equivSmallModel.{u + 1} S.Fppf).inverse.sheafInducedTopologyEquivOfIsCoverDense
      (smallFppfTopology S) Ab.{u + 1})

instance hasExt_sheaf_smallFppfTopology :
    HasExt.{u + 1} (Sheaf (smallFppfTopology S) Ab.{u + 1}) :=
  IsGrothendieckAbelian.hasExt _

noncomputable def fppfCohomology (F : Sheaf (smallFppfTopology S) Ab.{u + 1}) (n : ℕ) :
    Type (u + 1) :=
  F.H n

noncomputable instance (F : Sheaf (smallFppfTopology S) Ab.{u + 1}) (n : ℕ) :
    AddCommGroup (fppfCohomology S F n) :=
  inferInstanceAs <| AddCommGroup (F.H n)

instance : (Functor.const (S.Fppf)ᵒᵖ : Ab.{u + 1} ⥤ ((S.Fppf)ᵒᵖ ⥤ Ab.{u + 1})).Additive where
  map_add := by intros; ext; rfl

instance : (constantSheaf (smallFppfTopology S) Ab.{u + 1}).Additive :=
  inferInstanceAs
    (Functor.const (S.Fppf)ᵒᵖ ⋙ presheafToSheaf (smallFppfTopology S) Ab.{u + 1}).Additive

universe w in

noncomputable def homULiftIntAddEquiv (A : Ab.{w}) :
    (AddCommGrpCat.of (ULift.{w} ℤ) ⟶ A) ≃+ A :=
  { ConcreteCategory.homEquiv.trans (uliftZMultiplesHom A.carrier).symm with
    map_add' := fun f g => by
      have h : ConcreteCategory.homEquiv (f + g) =
          ConcreteCategory.homEquiv f + ConcreteCategory.homEquiv g := rfl
      show (uliftZMultiplesHom A.carrier).symm (ConcreteCategory.homEquiv (f + g)) = _
      rw [h]
      rfl }

open Abelian in

noncomputable def sheafHZeroAddEquiv (F : Sheaf (smallFppfTopology S) Ab.{u + 1}) :
    F.H 0 ≃+ F.obj.obj (op (fppfTerminal S)) :=
  (Ext.addEquiv₀.trans
    ((constantSheafAdj _ _ (fppfTerminalIsTerminal S)).homAddEquiv _ _)).trans
    (homULiftIntAddEquiv.{u + 1} (F.obj.obj (op (fppfTerminal S))))

open Abelian in

noncomputable def fppfCohomologyZeroAddEquiv (F : Sheaf (smallFppfTopology S) Ab.{u + 1}) :
    fppfCohomology S F 0 ≃+ F.obj.obj (op (fppfTerminal S)) :=
  sheafHZeroAddEquiv S F

open Abelian in

noncomputable def sheafHMap {F G : Sheaf (smallFppfTopology S) Ab.{u + 1}} (φ : F ⟶ G)
    (n : ℕ) : F.H n →+ G.H n :=
  AddMonoidHom.mk' (fun α => Ext.comp α (Ext.mk₀ φ) (add_zero n))
    (fun α β => by exact Ext.add_comp α β (Ext.mk₀ φ) (add_zero n))

open Abelian in

noncomputable def fppfCohomologyMap {F G : Sheaf (smallFppfTopology S) Ab.{u + 1}} (φ : F ⟶ G)
    (n : ℕ) : fppfCohomology S F n →+ fppfCohomology S G n :=
  sheafHMap S φ n

open Abelian in

theorem sheafHMap_id {F : Sheaf (smallFppfTopology S) Ab.{u + 1}} (n : ℕ)
    (α : F.H n) :
    sheafHMap S (𝟙 F) n α = α := by
  show Ext.comp α (Ext.mk₀ (𝟙 F)) (add_zero n) = α
  exact Ext.comp_mk₀_id α

open Abelian in

theorem fppfCohomologyMap_id {F : Sheaf (smallFppfTopology S) Ab.{u + 1}} (n : ℕ)
    (α : fppfCohomology S F n) :
    fppfCohomologyMap S (𝟙 F) n α = α :=
  sheafHMap_id S n α

open Abelian in

theorem sheafHMap_comp {F G H' : Sheaf (smallFppfTopology S) Ab.{u + 1}}
    (φ : F ⟶ G) (ψ : G ⟶ H') (n : ℕ) (α : F.H n) :
    sheafHMap S (φ ≫ ψ) n α = sheafHMap S ψ n (sheafHMap S φ n α) := by
  show Ext.comp α (Ext.mk₀ (φ ≫ ψ)) (add_zero n) =
    Ext.comp (Ext.comp α (Ext.mk₀ φ) (add_zero n)) (Ext.mk₀ ψ) (add_zero n)
  rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero]

open Abelian in

theorem fppfCohomologyMap_comp {F G H' : Sheaf (smallFppfTopology S) Ab.{u + 1}}
    (φ : F ⟶ G) (ψ : G ⟶ H') (n : ℕ) (α : fppfCohomology S F n) :
    fppfCohomologyMap S (φ ≫ ψ) n α = fppfCohomologyMap S ψ n (fppfCohomologyMap S φ n α) :=
  sheafHMap_comp S φ ψ n α

noncomputable def fppfCohomologyFunctor (n : ℕ) :
    Sheaf (smallFppfTopology S) Ab.{u + 1} ⥤ Ab.{u + 1} :=
  Sheaf.functorH (smallFppfTopology S) n

theorem fppfCohomologyFunctor_obj_carrier (n : ℕ) (F : Sheaf (smallFppfTopology S) Ab.{u + 1}) :
    ((fppfCohomologyFunctor S n).obj F : Type (u + 1)) = F.H n :=
  rfl

noncomputable def fppfBigToOverRestriction :
    Sheaf fppfTopology.{u} Ab.{u + 1} ⥤ Sheaf (fppfTopology.{u}.over S) Ab.{u + 1} :=
  fppfTopology.overPullback Ab.{u + 1} S

noncomputable def fppfSmallToOverPushforward :
    Sheaf (smallFppfTopology S) Ab.{u + 1} ⥤ Sheaf (fppfTopology.{u}.over S) Ab.{u + 1} :=
  (Fppf.forget S).sheafPushforwardCocontinuous Ab.{u + 1} (smallFppfTopology S)
    (fppfTopology.over S)

open ZeroObject in

theorem gate_zero_sheaf_subsingleton (n : ℕ) :
    Subsingleton (fppfCohomology S (0 : Sheaf (smallFppfTopology S) Ab.{u + 1}) n) := by
  show Subsingleton ((0 : Sheaf (smallFppfTopology S) Ab.{u + 1}).H n)
  exact Sheaf.subsingleton_H_of_isZero (Limits.isZero_zero _) n

theorem gate_H0_nontrivial_of_sections_nontrivial (F : Sheaf (smallFppfTopology S) Ab.{u + 1})
    (h : Nontrivial (F.obj.obj (op (fppfTerminal S)))) :
    Nontrivial (fppfCohomology S F 0) :=
  (fppfCohomologyZeroAddEquiv S F).toEquiv.nontrivial

open ZeroObject in

theorem gate_H0_equiv_fires_on_zero_sheaf :
    Subsingleton
      (((0 : Sheaf (smallFppfTopology S) Ab.{u + 1}).obj.obj (op (fppfTerminal S))) :
        Type (u + 1)) :=
  have : Subsingleton (fppfCohomology S (0 : Sheaf (smallFppfTopology S) Ab.{u + 1}) 0) :=
    gate_zero_sheaf_subsingleton S 0
  (fppfCohomologyZeroAddEquiv S
    (0 : Sheaf (smallFppfTopology S) Ab.{u + 1})).symm.toEquiv.subsingleton

section SpecInt

noncomputable abbrev specInt : Scheme.{0} := Spec (CommRingCat.of ℤ)

noncomputable example (F : Sheaf (smallFppfTopology specInt) Ab.{1}) :
    AddCommGroup (fppfCohomology specInt F 1) :=
  inferInstance

open Abelian in

noncomputable def fppfCohomologySpecIntZeroAddEquiv
    (F : Sheaf (smallFppfTopology specInt) Ab.{1}) :
    fppfCohomology specInt F 0 ≃+ F.obj.obj (op (fppfTerminal specInt)) :=
  fppfCohomologyZeroAddEquiv specInt F

open ZeroObject in

theorem gate_specInt_H1_zero_sheaf_subsingleton :
    Subsingleton (fppfCohomology specInt (0 : Sheaf (smallFppfTopology specInt) Ab.{1}) 1) :=
  gate_zero_sheaf_subsingleton specInt 1

end SpecInt

end AlgebraicGeometry.Scheme
