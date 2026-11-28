import Lemma.Fin.Any_In_BraceCastAdd__NatAdd
import Lemma.Fin.CastAdd.ne.NatAdd
import Lemma.Fin.InjectiveNatAdd
import Lemma.Matrix.MulDotMul__RotaryOn.eq.Dot_MulRotaryOn__Sub.of.All_EqSum__Add.All_Any_In_Brace.All_Ne.Injective.Injective
import Lemma.Real.Sum.eq.Add_Sum
open Fin Matrix Real
open scoped Matrix


/--
Half-split rotations collapse to relative angles under the dot product:
\((R_\alpha q) \cdot (R_\beta k) = q \cdot (R_{\beta - \alpha} k)\).
-/
@[path]
private lemma main
  {d : ℕ}
-- given
  (α β : Fin d → ℝ)
  (q k : Fin (d + d) → ℝ) :
-- imply
  Matrix.rotary α *ᵥ q ⬝ᵥ Matrix.rotary β *ᵥ k =
    q ⬝ᵥ Matrix.rotary (β - α) *ᵥ k := by
-- proof
  simpa [Matrix.rotary] using
    MulDotMul__RotaryOn.eq.Dot_MulRotaryOn__Sub.of.All_EqSum__Add.All_Any_In_Brace.All_Ne.Injective.Injective
      (Fin.castAdd_injective d d) (InjectiveNatAdd d) CastAdd.ne.NatAdd Any_In_BraceCastAdd__NatAdd
      (Sum.eq.Add_Sum (d := d)) α β q k


-- created on 2026-11-27
-- updated on 2026-11-28
