import Lemma.Definitions.Def_FullLevelTate_Datum
import Lemma.Definitions.Def_DrinfeldCurve_TateRep

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace FullLevelTate

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} {O' : Type} [CommRing O'] [IsLocalRing O']

structure Datum.DrinfeldSpecialization (D : Datum q M' O') (K : Type) [Field K] [Algebra O' K]
    (lam : ℕ) [Fact lam.Prime] [Algebra ℚ_[lam] K]
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)] : Type 1 where

  index : Type
  [instFinite : Finite index]

  sp : K ⊗[O'] D.V →ₗ[K] DrinfeldCurve.tateProd q k lam K index

attribute [instance] Datum.DrinfeldSpecialization.instFinite

end FullLevelTate

end
