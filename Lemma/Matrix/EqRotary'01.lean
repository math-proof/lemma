import Lemma.Fin.Any_In_BraceRopeEven__RopeOdd
import Lemma.Fin.InjectiveRopeEven
import Lemma.Fin.InjectiveRopeOdd
import Lemma.Fin.RopeEven.ne.RopeOdd
import Lemma.Matrix.EqRotaryOn__01.of.All_Any_In_Brace.All_Ne.Injective.Injective
import Mathlib
open Fin Matrix


/-- The interleaved rotary matrix at zero angle is the identity matrix. -/
@[path]
private lemma main
  {d : ℕ} :
-- imply
  Matrix.rotary' (0 : Fin d → ℝ) = 1 := by
-- proof
  simpa [Matrix.rotary'] using
    EqRotaryOn__01.of.All_Any_In_Brace.All_Ne.Injective.Injective (InjectiveRopeEven d) (InjectiveRopeOdd d)
      (RopeEven.ne.RopeOdd d) (Any_In_BraceRopeEven__RopeOdd d)


-- created on 2026-11-25
