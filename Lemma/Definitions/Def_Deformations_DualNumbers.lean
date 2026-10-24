import Mathlib
import Lemma.Definitions.Def_Deformations_ProartinianCat

set_option autoImplicit false

universe u

open CategoryTheory IsLocalRing TrivSqZeroExt
open scoped DualNumber

namespace Deformation

local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)

namespace ProartinianCat

variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]

instance : Module.Finite (𝓴 𝓞) ((𝓴 𝓞)[ε]) :=
  inferInstanceAs (Module.Finite (𝓴 𝓞) ((𝓴 𝓞) × (𝓴 𝓞)))

instance : IsArtinianRing ((𝓴 𝓞)[ε]) :=
  IsArtinianRing.of_finite (𝓴 𝓞) ((𝓴 𝓞)[ε])

instance : TopologicalSpace ((𝓴 𝓞)[ε]) := ⊥

instance : DiscreteTopology ((𝓴 𝓞)[ε]) := ⟨rfl⟩

instance : IsLocalHom (algebraMap 𝓞 ((𝓴 𝓞)[ε])) where
  map_nonunit a ha := by
    rw [show algebraMap 𝓞 ((𝓴 𝓞)[ε]) a = TrivSqZeroExt.inl (algebraMap 𝓞 (𝓴 𝓞) a) from rfl,
      TrivSqZeroExt.isUnit_inl_iff] at ha
    exact (isUnit_map_iff (algebraMap 𝓞 (𝓴 𝓞)) a).mp ha

lemma residue_inl_fst_eq (y : (𝓴 𝓞)[ε]) :
    residue ((𝓴 𝓞)[ε]) (TrivSqZeroExt.inl y.fst) = residue ((𝓴 𝓞)[ε]) y := by
  refine Ideal.Quotient.eq.mpr ?_
  have h3 : TrivSqZeroExt.inl y.fst - y = -TrivSqZeroExt.inr y.snd := by
    ext <;> simp
  rw [h3]
  refine neg_mem (IsLocalRing.mem_maximalIdeal _ |>.mpr ?_)
  rw [mem_nonunits_iff, TrivSqZeroExt.isUnit_inr_iff]
  exact fun h => (not_subsingleton (𝓴 𝓞)) h

instance : IsResidueAlgebra 𝓞 ((𝓴 𝓞)[ε]) where
  isSurjective' := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := 𝓞) y.fst
    refine ⟨a, ?_⟩
    have h1 : algebraMap 𝓞 ((𝓴 𝓞)[ε]) a = TrivSqZeroExt.inl y.fst := by
      rw [show algebraMap 𝓞 ((𝓴 𝓞)[ε]) a = TrivSqZeroExt.inl (algebraMap 𝓞 (𝓴 𝓞) a) from rfl,
        show algebraMap 𝓞 (𝓴 𝓞) a = residue 𝓞 a from rfl, ha]
    calc algebraMap 𝓞 (𝓴 ((𝓴 𝓞)[ε])) a
        = residue ((𝓴 𝓞)[ε]) (algebraMap 𝓞 ((𝓴 𝓞)[ε]) a) := rfl
      _ = residue ((𝓴 𝓞)[ε]) (TrivSqZeroExt.inl y.fst) := by rw [h1]
      _ = (Ideal.Quotient.mk (maximalIdeal ((𝓴 𝓞)[ε]))) y := residue_inl_fst_eq 𝓞 y

instance : IsLocalProartinianAlgebra 𝓞 ((𝓴 𝓞)[ε]) := ⟨⟩

noncomputable def dualNumbers : ProartinianCat 𝓞 :=
  .of 𝓞 ((𝓴 𝓞)[ε])

instance : DiscreteTopology (dualNumbers 𝓞) :=
  inferInstanceAs (DiscreteTopology ((𝓴 𝓞)[ε]))

noncomputable def dualNumbersFst : dualNumbers 𝓞 ⟶ residueField where
  hom := ⟨TrivSqZeroExt.fstHom 𝓞 (𝓴 𝓞) (𝓴 𝓞), continuous_of_discreteTopology⟩

lemma eq_dualNumbersFst (f : dualNumbers 𝓞 ⟶ residueField) : f = dualNumbersFst 𝓞 :=
  Subsingleton.elim _ _

end ProartinianCat

end Deformation
