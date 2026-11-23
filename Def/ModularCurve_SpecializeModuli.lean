module

public import Mathlib
public import Theorem.HahnSeries.JqCoeff
public import Theorem.Ideal.RatFuncPlaces
public import Abbrev.ModularCurve_SpecializeModuli

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicCurve Ideal

namespace ModularCurve

section Transcendence

variable (K : Type*) [Field K]

def ratFuncEquivCharLOneC : RatFunc K ≃ₐ[K] (modularFunctionFieldC K 1) :=
  (RatFunc.algEquivOfTranscendental (jqModC K) (transcendental_jqModC K)).trans
    (IntermediateField.equivOfEq (modularFunctionFieldC_one K).symm)

end Transcendence

section Jacobian

variable (K : Type*) [Field K]

def charLGeomPlaceEquiv :
    Place K (RatFunc K) ≃ Place K (modularFunctionFieldC K 1) :=
  Place.congrEquiv (ratFuncEquivCharLOneC K).toRingEquiv
    (fun a => (ratFuncEquivCharLOneC K).commutes a)

def charLGeomPlaceOfPoint (a : K) : Place K (modularFunctionFieldC K 1) :=
  charLGeomPlaceEquiv K (RationalFunctionField.placeOfPoint K a)

def charLGeomModuliDictionary :
    (K →₀ ℤ) →+ Divisor K (modularFunctionFieldC K 1) :=
  Finsupp.mapDomain.addMonoidHom (charLGeomPlaceOfPoint K)

end Jacobian

section Map

variable {K k : Type*} [Field K] [Field k]

def specializePlace (r : K → k) (a : K) : Place k (modularFunctionFieldC k 1) :=
  charLGeomPlaceOfPoint k (r a)

omit [Field K] in
def specializeModuli (r : K → k) :
    (K →₀ ℤ) →+ Divisor k (modularFunctionFieldC k 1) :=
  (charLGeomModuliDictionary k).comp (Finsupp.mapDomain.addMonoidHom r)

omit [Field K] in

end Map

section Degree

variable {K k : Type*} [Field K] [Field k]

omit [Field K] in

end Degree

section Galois

variable {K k : Type*} [Field K] [Field k]

omit [Field K] in

end Galois

end ModularCurve

end
