import Mathlib
import Lemma.Definitions.Def_NumberField_SIdeleModule

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

namespace NumberField.SArchIdele

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
variable (S : Finset (HeightOneSpectrum (𝓞 E)))

abbrev Index : Type := {v // v ∈ S} ⊕ InfinitePlace E

noncomputable def fibre : Index E S → Rep ℤ (K ≃ₐ[E] K) :=
  Sum.elim (fun v => NumberField.FiniteSIdele.fibre E K S (Sum.inl v)) (NumberField.ArchIdele.fibre E K)

@[simp] theorem fibre_inl (v : {v // v ∈ S}) : fibre E K S (Sum.inl v) = NumberField.FiniteSIdele.fibre E K S (Sum.inl v) := rfl

@[simp] theorem fibre_inr (v : InfinitePlace E) : fibre E K S (Sum.inr v) = NumberField.ArchIdele.fibre E K v := rfl

theorem fibre_inl_eq_coind (v : {v // v ∈ S}) :
    fibre E K S (Sum.inl v) =
      Rep.coind (NumberField.FiniteSIdele.D E K v.1).subtype (NumberField.FiniteSIdele.localUnits E K v.1) := rfl

theorem fibre_inr_eq_coind (v : InfinitePlace E) :
    fibre E K S (Sum.inr v) =
      Rep.coind (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)).subtype
        (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)) := rfl

noncomputable abbrev obj : Rep ℤ (K ≃ₐ[E] K) := GroupCohomology.RepPi.obj (fibre E K S)

noncomputable abbrev proj (i : Index E S) : obj E K S ⟶ fibre E K S i := GroupCohomology.RepPi.proj (fibre E K S) i

noncomputable def toSIdeleComponent : (i : NumberField.SIdele.Index E S) → (obj E K S ⟶ NumberField.SIdele.fibre E K S i)
  | Sum.inl (Sum.inl v) => proj E K S (Sum.inl v)
  | Sum.inl (Sum.inr _) => 0
  | Sum.inr v => proj E K S (Sum.inr v)

noncomputable def toSIdele : obj E K S ⟶ NumberField.SIdele.obj E K S :=
  GroupCohomology.RepPi.lift (NumberField.SIdele.fibre E K S) (toSIdeleComponent E K S)

@[simp] theorem toSIdele_hom_apply_inl_inl (x : obj E K S) (v : {v // v ∈ S}) :
    (toSIdele E K S).hom x (Sum.inl (Sum.inl v)) = x (Sum.inl v) := rfl

@[simp] theorem toSIdele_hom_apply_inl_inr (x : obj E K S) (v : {v // v ∉ S}) :
    (toSIdele E K S).hom x (Sum.inl (Sum.inr v)) = 0 := rfl

@[simp] theorem toSIdele_hom_apply_inr (x : obj E K S) (v : InfinitePlace E) :
    (toSIdele E K S).hom x (Sum.inr v) = x (Sum.inr v) := rfl

theorem toSIdele_injective : Function.Injective (toSIdele E K S).hom := by
  intro x y h
  funext i
  cases i with
  | inl v => exact congrFun h (Sum.inl (Sum.inl v))
  | inr v => exact congrFun h (Sum.inr v)

noncomputable def diagSComponent : (i : Index E S) → (NumberField.SUnits.sUnitsRep E K S ⟶ fibre E K S i)
  | Sum.inl v => NumberField.SUnits.diagIn E K S v
  | Sum.inr v => NumberField.SIdele.diagInf E K S v

noncomputable def diagS : NumberField.SUnits.sUnitsRep E K S ⟶ obj E K S :=
  GroupCohomology.RepPi.lift (fibre E K S) (diagSComponent E K S)

theorem diagS_hom_apply_inl (x : NumberField.SUnits.sUnitsRep E K S) (v : {v // v ∈ S}) :
    (diagS E K S).hom x (Sum.inl v) = (NumberField.SUnits.diagIn E K S v).hom x := rfl

theorem diagS_hom_apply_inr (x : NumberField.SUnits.sUnitsRep E K S) (v : InfinitePlace E) :
    (diagS E K S).hom x (Sum.inr v) = (NumberField.SIdele.diagInf E K S v).hom x := rfl

theorem toSIdele_diagS_apply_inl_inl (x : NumberField.SUnits.sUnitsRep E K S) (v : {v // v ∈ S}) :
    (toSIdele E K S).hom ((diagS E K S).hom x) (Sum.inl (Sum.inl v)) = (NumberField.SIdele.diag E K S).hom x (Sum.inl (Sum.inl v)) := rfl

theorem toSIdele_diagS_apply_inr (x : NumberField.SUnits.sUnitsRep E K S) (v : InfinitePlace E) :
    (toSIdele E K S).hom ((diagS E K S).hom x) (Sum.inr v) = (NumberField.SIdele.diag E K S).hom x (Sum.inr v) := rfl

theorem toSIdele_diagS_apply_inl_inr (x : NumberField.SUnits.sUnitsRep E K S) (v : {v // v ∉ S}) :
    (toSIdele E K S).hom ((diagS E K S).hom x) (Sum.inl (Sum.inr v)) = 0 := rfl

end NumberField.SArchIdele
