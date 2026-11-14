import Def.CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Def.CerednikDrinfeld_AlgFunctorConst

set_option autoImplicit false

namespace CerednikDrinfeld.FormalOmega.AlgFunctor

variable {𝒪 : Type} [CommRing 𝒪]


@[simp] theorem const_map (X : Type) {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (φ : B →ₐ[𝒪] B') (x : X) : (const (𝒪 := 𝒪) X).map φ x = x := rfl

end CerednikDrinfeld.FormalOmega.AlgFunctor
