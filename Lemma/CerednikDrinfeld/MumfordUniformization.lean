import Class.CerednikDrinfeld_MumfordPeriod
import Def.CerednikDrinfeld_JPrimeTorsionDatum
import Instance.ValuationSubring_CompletionDecompositionAction
import Lemma.EllipticCurve.FrobeniusTrace
import Def.FLTPrelim_Ramification
import Lemma.Compat.Mathlib430
import Def.CerednikDrinfeld_MumfordUniformization
import Structure.CerednikDrinfeld_MumfordUniformization

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld
namespace Mumford

open ModularCurve

variable {E V : Type} [Fintype E] [DecidableEq V]

namespace PeriodDatum

variable {D : DegeneracyData E V} {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}


@[simp] theorem coeffMap_apply (P : PeriodDatum D K L ord) (s : L →+* L) (u : P.TorusPoints)
    (z : ↥(ribbonKernel D)) :
    P.coeffMap s u z = Additive.ofMul (Units.map (s : L →* L) (Additive.toMul (u z))) := rfl


@[simp] theorem precomp_apply (P : PeriodDatum D K L ord) (f : ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D))
    (u : P.TorusPoints) (z : ↥(ribbonKernel D)) : P.precomp f u z = u (f z) := rfl

end PeriodDatum


end Mumford

end CerednikDrinfeld

end
