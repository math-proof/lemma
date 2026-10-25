import Def.M4aHerbrand_ArchSemilocal
import Lemma.M4aHerbrand.FiniteConorm
import Def.M4aHerbrand_GenuineBeta

noncomputable section

namespace M4aHerbrand.Bridge

open NumberField IsDedekindDomain M4aHerbrand.ArchSemilocal

section Genuine

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


@[simp] theorem genuineβ_fst (x : AdeleRing (𝓞 K) K) :
    (genuineβ K L x).1 = (genuineInfinitePlaceData (K := K) (L := L)).conorm x.1 := rfl

@[simp] theorem genuineβ_snd (x : AdeleRing (𝓞 K) K) :
    (genuineβ K L x).2 = finiteConorm (𝓞 K) K L (𝓞 L) x.2 := rfl

theorem continuous_genuineβ : Continuous (genuineβ K L) :=
  Continuous.prodMap continuous_conorm (continuous_finiteConorm (𝓞 K) K L (𝓞 L))

theorem genuineβ_compat (e : K) :
    genuineβ K L (algebraMap K (AdeleRing (𝓞 K) K) e) = algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L e) :=
  Prod.ext ((genuineInfinitePlaceData (K := K) (L := L)).conorm_algebraMap e)
    (finiteConorm_algebraMap (𝓞 K) K L (𝓞 L) e)

end Genuine

end M4aHerbrand.Bridge

end
