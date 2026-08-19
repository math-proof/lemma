import Lemma.Tensor.OfVectorMapToVector.eq.Stack
import Lemma.Tensor.Select.eq.OfVectorMapToVector.of.GtLength
open Tensor


@[main]
private lemma main
  {d : ℕ}
-- given
  (h : s.length > d)
  (X : Tensor α (n :: s))
  (i : Fin s[d]) :
-- imply
  X.select ⟨d + 1, by grind⟩ ⟨i, by grind⟩ = [k < n] (X[k].select ⟨d, by grind⟩ i) := by
-- proof
  rw [Select.eq.OfVectorMapToVector.of.GtLength h]
  apply OfVectorMapToVector.eq.Stack (fun s => s.eraseIdx d)


-- created on 2025-11-15
