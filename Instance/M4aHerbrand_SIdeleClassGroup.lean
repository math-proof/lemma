-- Carved from Lemma/Definitions/Def_M4aHerbrand_SIdeleClassGroup.lean: instance decls only.
module

public import Mathlib
public import Def.M4aHerbrand_IdeleClassVocab
public import Theorem.Set.FiniteUnitIdelesOutside
public import Theorem.Set.SIdeleClassGroup
public import Def.NumberField_SIdeleClassGroup
@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain CategoryTheory

noncomputable section

namespace M4aHerbrand

section comm

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

instance isMulCommutative_ideleClassGroup : IsMulCommutative (IdeleClassGroup R F) := ⟨⟨fun a b => mul_comm a b⟩⟩

end comm


section SClass

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

instance isMulCommutative_sIdeleClassGroup (T : Set (HeightOneSpectrum R)) :
    IsMulCommutative (SIdeleClassGroup R F T) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩


end SClass


end M4aHerbrand


end
