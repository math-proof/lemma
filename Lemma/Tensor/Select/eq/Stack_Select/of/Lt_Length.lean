import Lemma.Tensor.FromVectorMapToVector.eq.Stack
import Lemma.Tensor.Select.eq.FromVectorMap_FunSelect.of.Lt_Length
open Tensor


@[main]
private lemma main
  {d : ℕ}
-- given
  (h : d < s.length)
  (X : Tensor α (n :: s))
  (i : Fin s[d]) :
-- imply
  X.select ⟨d + 1, by grind⟩ ⟨i, by grind⟩ = [k < n] (X[k].select ⟨d, by grind⟩ i) := by
-- proof
  rw [Select.eq.FromVectorMap_FunSelect.of.Lt_Length h]
  apply FromVectorMapToVector.eq.Stack (fun s => s.eraseIdx d)


-- created on 2025-11-15
