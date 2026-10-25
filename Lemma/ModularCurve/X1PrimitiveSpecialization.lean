import Mathlib
import Def.FLTPrelim_Ramification
import Lemma.ModularCurve.X1Diamond
import Lemma.EllipticCurve.TateModule
import Def.ModularCurve_X1PrimitiveSpecialization
import Structure.ModularCurve_X1PrimitiveSpecialization

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve CongruenceSubgroup

namespace ModularCurve

section NormFree


theorem mem_primitiveReps {M₀ q c d : ℕ} :
    d ∈ primitiveReps M₀ q c ↔
      d < M₀ * q ^ c ∧ Nat.Coprime d (M₀ * q ^ c) ∧ d ≡ 1 [MOD M₀ * q ^ (c - 1)] := by
  rw [primitiveReps, Finset.mem_filter, Finset.mem_range]

variable (M : ℕ)


@[simp]
theorem normFreeEnd_apply (S : Finset ℕ) (x : JOne M) :
    normFreeEnd M S x = S.card • x - ∑ d ∈ S, diamondOneBar M d x :=
  rfl


theorem mem_primitivePart {M₀ q c : ℕ} {y : JOne (M₀ * q ^ c)} :
    y ∈ primitivePart M₀ q c ↔ ∃ x, normFreeEnd (M₀ * q ^ c) (primitiveReps M₀ q c) x = y :=
  AddMonoidHom.mem_range

theorem normFreeEnd_mem_primitivePart {M₀ q c : ℕ} (x : JOne (M₀ * q ^ c)) :
    normFreeEnd (M₀ * q ^ c) (primitiveReps M₀ q c) x ∈ primitivePart M₀ q c :=
  ⟨x, rfl⟩

end NormFree

section Datum

variable (M₀ q c : ℕ) (P : ValuationSubring (AlgebraicClosure ℚ))
variable (k : Type) [Field k] (π : P →+* k)


end Datum

end ModularCurve

end
