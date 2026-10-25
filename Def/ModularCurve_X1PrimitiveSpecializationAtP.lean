import Mathlib
import Def.FLTPrelim_Ramification
import Instance.EllipticCurve_FrobeniusTrace
import Instance.EllipticCurve_TateModule
import Lemma.ModularCurve.X1HeckeModule
import Def.ModularCurve_X1PrimitiveSpecialization
import Lemma.ModularCurve.QExpFrobeniusModL

set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve CongruenceSubgroup

namespace ModularCurve

section NormFree

variable (M p : ℕ)

def normFreeRepsAt : Finset ℕ :=
  (Finset.range M).filter (fun d => Nat.Coprime d M ∧ d ≡ 1 [MOD M / p])


def normFreePartAt : AddSubgroup (JOne M) :=
  (normFreeEnd M (normFreeRepsAt M p)).range

end NormFree

end ModularCurve

end
