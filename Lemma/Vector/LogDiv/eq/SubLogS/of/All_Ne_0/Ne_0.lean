import Lemma.Real.LogDiv.eq.SubLogS.of.Ne_0.Ne_0
import Lemma.Vector.GetDiv.eq.DivGet
import Lemma.Vector.GetSub.eq.SubGet
import sympy.vector.functions
open Real Vector


@[main]
private lemma main
  [LogPos α]
  {x : List.Vector α n}
  {y : α}
-- given
  (h₀ : ∀ i : Fin n, x[i] ≠ 0)
  (h₁ : y ≠ 0) :
-- imply
  log (x / y) = log x - log y := by
-- proof
  ext i
  rw [GetSub.eq.SubGet.fin]
  simp [Log.log]
  rw [GetDiv.eq.DivGet.fin]
  apply LogDiv.eq.SubLogS.of.Ne_0.Ne_0
  ·
    apply h₀
  ·
    apply h₁


-- created on 2025-12-04
