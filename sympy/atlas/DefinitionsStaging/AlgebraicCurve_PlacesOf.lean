import Mathlib.AlgebraicGeometry.FunctionField
import Lemma.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Lemma.Definitions.Def_AlgebraicCurve_CurveModel
import Def.AlgebraicCurve_PlacesOf

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve

variable {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C]


theorem mem_placesOf_iff (U : C.Opens) :
    letI := (baseToFunctionField c).toAlgebra
    ∀ v : Place K C.functionField, v ∈ placesOf c U ↔ ∃ x : C, x ∈ U ∧ IsClosed ({x} : Set C) ∧
      (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring :=
  fun _ => Iff.rfl

theorem placesOf_mono {U V : C.Opens} (h : U ≤ V) :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c U ⊆ placesOf c V := by
  rintro v ⟨x, hxU, hx, hv⟩
  exact ⟨x, h hxU, hx, hv⟩

theorem placesOf_sup (U V : C.Opens) :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c (U ⊔ V) = placesOf c U ∪ placesOf c V := by
  letI := (baseToFunctionField c).toAlgebra
  apply Set.Subset.antisymm
  · rintro v ⟨x, hxUV, hx, hv⟩
    rcases (show x ∈ (U : Set C) ∪ (V : Set C) from hxUV) with h | h
    · exact Or.inl ⟨x, h, hx, hv⟩
    · exact Or.inr ⟨x, h, hx, hv⟩
  · rintro v (h | h)
    · exact placesOf_mono c le_sup_left h
    · exact placesOf_mono c le_sup_right h

theorem placesOf_bot :
    letI := (baseToFunctionField c).toAlgebra
    placesOf c (⊥ : C.Opens) = ∅ := by
  letI := (baseToFunctionField c).toAlgebra
  ext v
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨x, hx, -, -⟩
  exact hx

end AlgebraicCurve

end
