/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/HyperfactorialPartition.lean -/
module

public import Structure.NumberTheory.HyperfactorialPartition
public import Def.MathlibExtTest.NumberTheory.HyperfactorialPartition

public section

namespace MetaMathlibExt

example : ¬ (3 ≤ 2 * (0 + 1)) := by decide

example : ¬ HyperfactorialDigitsNormalized 2
    (fun i : Fin 2 => if i = 0 then 1 else 0) := by
  intro h
  simpa [HyperfactorialDigitsNormalized] using h (by decide)

end MetaMathlibExt
