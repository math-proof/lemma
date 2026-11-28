import Lemma.Fin.Any_In_BraceRopeEven__RopeOdd
import Lemma.Fin.InjectiveRopeEven
import Lemma.Fin.InjectiveRopeOdd
import Lemma.Fin.RopeEven.ne.RopeOdd
import Lemma.Fin.Sum.eq.AddSumS
import Lemma.Matrix.MulDotMul__RotaryOn.eq.Dot_MulRotaryOn__Sub.of.All_EqSum__Add.All_Any_In_Brace.All_Ne.Injective.Injective
open Fin Matrix Real
open scoped Matrix


/--
Interleaved rotations collapse to relative angles under the dot product:
\((R_\alpha q) \cdot (R_\beta k) = q \cdot (R_{\beta - \alpha} k)\).
-/
@[path]
private lemma main
  {d : ℕ}
-- given
  (α β : Fin d → ℝ)
  (q k : Fin (d + d) → ℝ) :
-- imply
  Matrix.rotary' α *ᵥ q ⬝ᵥ Matrix.rotary' β *ᵥ k =
    q ⬝ᵥ Matrix.rotary' (β - α) *ᵥ k := by
-- proof
  simpa [Matrix.rotary'] using
    MulDotMul__RotaryOn.eq.Dot_MulRotaryOn__Sub.of.All_EqSum__Add.All_Any_In_Brace.All_Ne.Injective.Injective
      (InjectiveRopeEven d) (InjectiveRopeOdd d) (RopeEven.ne.RopeOdd d)
      (Any_In_BraceRopeEven__RopeOdd d) Sum.eq.AddSumS α β q k


-- created on 2026-11-27
-- updated on 2026-11-28
