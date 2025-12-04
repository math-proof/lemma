import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Tensor.DataSub.eq.SubDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.LogDiv.eq.SubLogS.of.All_Ne_0.All_Ne_0
import sympy.tensor.functions
open Tensor Vector


@[main]
private lemma main
  [LogPos α]
  {X Y : Tensor α s}
-- given
  (h₀ : ∀ i : Fin s.prod, X.data[i] ≠ 0)
  (h₁ : ∀ i : Fin s.prod, Y.data[i] ≠ 0) :
-- imply
  log (X / Y) = log X - log Y := by
-- proof
  apply Eq.of.EqDataS
  rw [DataSub.eq.SubDataS]
  simp [Log.log]
  rw [DataDiv.eq.DivDataS]
  exact LogDiv.eq.SubLogS.of.All_Ne_0.All_Ne_0 h₀ h₁


-- created on 2025-12-04
