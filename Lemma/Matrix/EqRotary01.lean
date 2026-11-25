import Lemma.Fin.Any_In_BraceCastAdd__NatAdd
import Lemma.Fin.CastAdd.ne.NatAdd
import Lemma.Fin.InjectiveNatAdd
import Lemma.Matrix.EqRotaryOn__01.of.All_Any_In_Brace.All_Ne.Injective.Injective
import Mathlib
open Fin Matrix


/-- The rotary matrix at zero angle is the identity matrix. -/
@[path]
private lemma main
  {d : ℕ} :
-- imply
  Matrix.rotary (0 : Fin d → ℝ) = 1 := by
-- proof
  simpa [Matrix.rotary] using
    EqRotaryOn__01.of.All_Any_In_Brace.All_Ne.Injective.Injective (castAdd_injective d d) (InjectiveNatAdd d)
      CastAdd.ne.NatAdd Any_In_BraceCastAdd__NatAdd


-- created on 2026-11-25
