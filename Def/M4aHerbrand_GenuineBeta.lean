import Instance.M4aHerbrand_ArchSemilocal
import Lemma.M4aHerbrand.FiniteConorm

noncomputable section

namespace M4aHerbrand.Bridge

open NumberField IsDedekindDomain M4aHerbrand.ArchSemilocal

section Genuine

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def genuineβ : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
  RingHom.prodMap (genuineInfinitePlaceData (K := K) (L := L)).conorm (finiteConorm (𝓞 K) K L (𝓞 L))

end Genuine

end M4aHerbrand.Bridge

end
