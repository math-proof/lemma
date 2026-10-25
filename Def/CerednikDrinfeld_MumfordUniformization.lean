import Class.CerednikDrinfeld_MumfordPeriod
import Def.CerednikDrinfeld_JPrimeTorsionDatum
import Instance.ValuationSubring_CompletionDecompositionAction
import Instance.EllipticCurve_FrobeniusTrace
import Def.FLTPrelim_Ramification
import Instance.Compat_Mathlib430

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld
namespace Mumford

open ModularCurve

variable {E V : Type} [Fintype E] [DecidableEq V]

namespace PeriodDatum

variable {D : DegeneracyData E V} {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}

def coeffMap (P : PeriodDatum D K L ord) (s : L →+* L) : P.TorusPoints →ₗ[ℤ] P.TorusPoints :=
  LinearMap.llcomp ℤ ↥(ribbonKernel D) (Additive Lˣ) (Additive Lˣ)
    (MonoidHom.toAdditive (Units.map (s : L →* L))).toIntLinearMap


def precomp (P : PeriodDatum D K L ord) (f : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) :
    P.TorusPoints →ₗ[ℤ] P.TorusPoints :=
  LinearMap.lcomp ℤ (Additive Lˣ) f

end PeriodDatum

end Mumford

end CerednikDrinfeld

end
