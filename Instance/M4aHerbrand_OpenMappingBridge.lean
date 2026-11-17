-- Carved from Lemma/Definitions/Def_M4aHerbrand_OpenMappingBridge.lean: instance decls only.

module

public import Mathlib.Topology.Algebra.Group.OpenMapping
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

@[expose] public section

namespace M4aHerbrand.Bridge

open NumberField IsDedekindDomain TensorProduct


section Adele

variable (R E : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E]
variable (S F : Type*) [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F]
  [IsFractionRing S F]
variable [Algebra E F]

open scoped RestrictedProduct in

instance instT2SpaceAdeleRing : T2Space (AdeleRing S F) :=
  inferInstanceAs (T2Space (((v : InfinitePlace F) → v.Completion) ×
    Πʳ v : HeightOneSpectrum S, [v.adicCompletion F, v.adicCompletionIntegers F]))


end Adele

end M4aHerbrand.Bridge
