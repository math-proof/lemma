import Def.CerednikDrinfeld_FormalUpperHalfPlaneCharts

set_option autoImplicit false

namespace CerednikDrinfeld.FormalOmega.AlgFunctor

variable {𝒪 : Type} [CommRing 𝒪]

def const (X : Type) : AlgFunctor 𝒪 where
  obj _ := X
  map _ x := x
  map_id _ := rfl
  map_comp _ _ _ := rfl

end CerednikDrinfeld.FormalOmega.AlgFunctor
