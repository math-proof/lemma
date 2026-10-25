/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/HyperfactorialPartition.lean -/


import Structure.NumberTheory.HyperfactorialPartition
import Def.MathlibExtTest.NumberTheory.HyperfactorialPartition


namespace MetaMathlibExt

example : ¬ (3 ≤ 2 * (0 + 1)) := by decide

example : ¬ HyperfactorialDigitsNormalized 2
    (fun i : Fin 2 => if i = 0 then 1 else 0) := by
  intro h
  simpa [HyperfactorialDigitsNormalized] using h (by decide)

end MetaMathlibExt
