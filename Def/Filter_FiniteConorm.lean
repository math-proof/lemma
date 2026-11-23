module

public import Instance.DedekindDomain_Completion_BaseChange

@[expose] public section

noncomputable section

namespace M4aHerbrand.Bridge

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section AKLB

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]

include K L in
omit [IsFractionRing B L] in

def finiteLocalHom (w : HeightOneSpectrum B) : (w.under A).adicCompletion K →+* w.adicCompletion L :=
  (Extension.adicCompletionSemialgHom K L (⟨w, rfl⟩ : (w.under A).Extension B)).toRingHom

def finiteConorm : FiniteAdeleRing A K →+* FiniteAdeleRing B L :=
  RestrictedProduct.mapAlongRingHom
    (fun v : HeightOneSpectrum A => v.adicCompletion K)
    (fun w : HeightOneSpectrum B => w.adicCompletion L)
    (HeightOneSpectrum.under A) (tendsto_under_cofinite A K L B)
    (fun w => finiteLocalHom A K L B w)
    (Filter.Eventually.of_forall fun w => finiteLocalHom_mapsTo A K L B w)

end AKLB

end M4aHerbrand.Bridge

end

end
