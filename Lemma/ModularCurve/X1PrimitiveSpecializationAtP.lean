import Mathlib
import Def.FLTPrelim_Ramification
import Lemma.EllipticCurve.FrobeniusTrace
import Lemma.EllipticCurve.TateModule
import Lemma.ModularCurve.X1HeckeModule
import Lemma.ModularCurve.X1PrimitiveSpecialization
import Lemma.ModularCurve.QExpFrobeniusModL
import Def.ModularCurve_X1PrimitiveSpecializationAtP
import Structure.ModularCurve_X1PrimitiveSpecializationAtP

set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve CongruenceSubgroup

namespace ModularCurve

section NormFree

variable (M p : ℕ)


variable {M p} in
theorem mem_normFreeRepsAt {d : ℕ} :
    d ∈ normFreeRepsAt M p ↔ d < M ∧ Nat.Coprime d M ∧ d ≡ 1 [MOD M / p] := by
  rw [normFreeRepsAt, Finset.mem_filter, Finset.mem_range]


variable {M p} in
theorem mem_normFreePartAt {y : JOne M} :
    y ∈ normFreePartAt M p ↔ ∃ x, normFreeEnd M (normFreeRepsAt M p) x = y :=
  AddMonoidHom.mem_range

theorem normFreeEnd_mem_normFreePartAt (x : JOne M) :
    normFreeEnd M (normFreeRepsAt M p) x ∈ normFreePartAt M p :=
  ⟨x, rfl⟩

end NormFree

section Datum

variable (M p : ℕ) [Fact p.Prime] (P : ValuationSubring (AlgebraicClosure ℚ))
variable (k : Type) [Field k] [CharP k p]


end Datum

end ModularCurve

end
