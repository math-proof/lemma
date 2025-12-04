import Lemma.Real.LogDiv.eq.SubLogS.of.Ne_0.Ne_0
import Lemma.Vector.GetDiv.eq.DivGetS
import Lemma.Vector.GetSub.eq.SubGetS
import sympy.vector.functions
open Vector Real


@[main]
private lemma main
  [LogPos α]
  {x y : List.Vector α n}
-- given
  (h₀ : ∀ i : Fin n, x[i] ≠ 0)
  (h₁ : ∀ i : Fin n, y[i] ≠ 0) :
-- imply
  log (x / y) = log x - log y := by
-- proof
  ext i
  rw [GetSub.eq.SubGetS.fin]
  simp [Log.log]
  rw [GetDiv.eq.DivGetS.fin]
  apply LogDiv.eq.SubLogS.of.Ne_0.Ne_0
  ·
    apply h₀
  ·
    apply h₁


-- created on 2025-12-03
