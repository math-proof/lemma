import Lemma.Real.LogMul.eq.AddLogS.of.Ne_0.Ne_0
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.GetAdd.eq.AddGetS
import sympy.vector.functions
open Real Vector


@[main]
private lemma main
  [LogPos α]
  {x y : List.Vector α n}
-- given
  (h₀ : ∀ i : Fin n, x[i] ≠ 0)
  (h₁ : ∀ i : Fin n, y[i] ≠ 0) :
-- imply
  log (x * y) = log x + log y := by
-- proof
  ext i
  rw [GetAdd.eq.AddGetS.fin]
  simp [Log.log]
  rw [GetMul.eq.MulGetS.fin]
  apply LogMul.eq.AddLogS.of.Ne_0.Ne_0
  ·
    apply h₀
  ·
    apply h₁


-- created on 2025-12-03
