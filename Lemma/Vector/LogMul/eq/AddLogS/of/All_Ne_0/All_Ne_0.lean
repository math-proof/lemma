import Lemma.Vector.GetAdd.eq.AddGetS
import sympy.vector.functions
open Vector


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
  rw [LogPos.log_mul ]
  .
    apply h₀
  .
    apply h₁


-- created on 2025-12-03
