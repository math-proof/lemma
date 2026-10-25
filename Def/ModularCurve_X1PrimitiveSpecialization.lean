import Mathlib
import Def.FLTPrelim_Ramification
import Def.ModularCurve_X1Diamond
import Instance.EllipticCurve_TateModule

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve CongruenceSubgroup

namespace ModularCurve

section NormFree

def primitiveReps (M₀ q c : ℕ) : Finset ℕ :=
  (Finset.range (M₀ * q ^ c)).filter
    (fun d => Nat.Coprime d (M₀ * q ^ c) ∧ d ≡ 1 [MOD M₀ * q ^ (c - 1)])


variable (M : ℕ)

def normFreeEnd (S : Finset ℕ) : JOne M →+ JOne M where
  toFun x := S.card • x - ∑ d ∈ S, diamondOneBar M d x
  map_zero' := by simp
  map_add' x y := by
    rw [nsmul_add, Finset.sum_congr rfl fun d _ => map_add (diamondOneBar M d) x y,
      Finset.sum_add_distrib]
    abel


def primitivePart (M₀ q c : ℕ) : AddSubgroup (JOne (M₀ * q ^ c)) :=
  (normFreeEnd (M₀ * q ^ c) (primitiveReps M₀ q c)).range

end NormFree

end ModularCurve

end
