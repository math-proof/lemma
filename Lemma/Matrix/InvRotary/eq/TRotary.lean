import Lemma.Fin.Any_In_BraceCastAdd__NatAdd
import Lemma.Fin.CastAdd.ne.NatAdd
import Lemma.Fin.InjectiveNatAdd
import Lemma.Matrix.InvRotaryOn.eq.TRotaryOn.of.All_EqSum__Add.All_Any_In_Brace.All_Ne.Injective.Injective
import Lemma.Real.Sum.eq.Add_Sum
open Fin Matrix Real
open scoped Matrix


/-- The half-split rotary matrix is invertible with inverse its transpose: \(R(\theta)^{-1} = R(\theta)^{\mathsf{T}}\). -/
@[path]
private lemma main
  {d : ℕ}
-- given
  (φ : Fin d → ℝ) :
-- imply
  (Matrix.rotary φ)⁻¹ = (Matrix.rotary φ)ᵀ := by
-- proof
  simpa [Matrix.rotary] using
    InvRotaryOn.eq.TRotaryOn.of.All_EqSum__Add.All_Any_In_Brace.All_Ne.Injective.Injective (Fin.castAdd_injective d d)
      (InjectiveNatAdd d) CastAdd.ne.NatAdd Any_In_BraceCastAdd__NatAdd
      (Sum.eq.Add_Sum (d := d)) φ


-- created on 2026-11-27
