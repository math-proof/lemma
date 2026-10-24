import Lemma.Definitions.Def_DedekindDomain_Completion_BaseChange

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

theorem tendsto_under_cofinite :
    Filter.Tendsto (HeightOneSpectrum.under A : HeightOneSpectrum B → HeightOneSpectrum A)
      Filter.cofinite Filter.cofinite := by
  intro S hS
  exact preimage_comap_finite A K L B Sᶜ hS

def finiteLocalHom (w : HeightOneSpectrum B) : (w.under A).adicCompletion K →+* w.adicCompletion L :=
  (Extension.adicCompletionSemialgHom K L (⟨w, rfl⟩ : (w.under A).Extension B)).toRingHom

theorem finiteLocalHom_apply (w : HeightOneSpectrum B) (x : (w.under A).adicCompletion K) :
    finiteLocalHom A K L B w x =
      Extension.adicCompletionSemialgHom K L (⟨w, rfl⟩ : (w.under A).Extension B) x := rfl

theorem continuous_finiteLocalHom (w : HeightOneSpectrum B) : Continuous (finiteLocalHom A K L B w) :=
  Extension.adicCompletionSemialgHom_continuous K L (⟨w, rfl⟩ : (w.under A).Extension B)

theorem finiteLocalHom_mapsTo (w : HeightOneSpectrum B) :
    Set.MapsTo (finiteLocalHom A K L B w)
      ((w.under A).adicCompletionIntegers K : Set ((w.under A).adicCompletion K))
      (w.adicCompletionIntegers L : Set (w.adicCompletion L)) :=
  Set.mapsTo_iff_image_subset.2
    (Extension.adicCompletionSemialgHom_image_adicCompletionIntegers K L
      (⟨w, rfl⟩ : (w.under A).Extension B))

def finiteConorm : FiniteAdeleRing A K →+* FiniteAdeleRing B L :=
  RestrictedProduct.mapAlongRingHom
    (fun v : HeightOneSpectrum A => v.adicCompletion K)
    (fun w : HeightOneSpectrum B => w.adicCompletion L)
    (HeightOneSpectrum.under A) (tendsto_under_cofinite A K L B)
    (fun w => finiteLocalHom A K L B w)
    (Filter.Eventually.of_forall fun w => finiteLocalHom_mapsTo A K L B w)

@[simp] theorem finiteConorm_apply (x : FiniteAdeleRing A K) (w : HeightOneSpectrum B) :
    finiteConorm A K L B x w =
      Extension.adicCompletionSemialgHom K L (⟨w, rfl⟩ : (w.under A).Extension B) (x (w.under A)) :=
  rfl

theorem continuous_finiteConorm : Continuous (finiteConorm A K L B) :=
  RestrictedProduct.mapAlong_continuous
    (fun v : HeightOneSpectrum A => v.adicCompletion K)
    (fun w : HeightOneSpectrum B => w.adicCompletion L)
    (HeightOneSpectrum.under A) (tendsto_under_cofinite A K L B)
    (fun w x => finiteLocalHom A K L B w x)
    (Filter.Eventually.of_forall fun w => finiteLocalHom_mapsTo A K L B w)
    (fun w => continuous_finiteLocalHom A K L B w)

theorem finiteConorm_algebraMap (k : K) :
    finiteConorm A K L B (algebraMap K (FiniteAdeleRing A K) k) =
      algebraMap L (FiniteAdeleRing B L) (algebraMap K L k) := by
  refine FiniteAdeleRing.ext L fun w => ?_
  rw [FiniteAdeleRing.algebraMap_apply]
  exact (Extension.adicCompletionSemialgHom K L (⟨w, rfl⟩ : (w.under A).Extension B)).commutes k

end AKLB

end M4aHerbrand.Bridge

end
