/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PRecursiveSequence.lean -/
module

public import Def.NumberTheory.PRecursiveSequence

public section

namespace MetaMathlibExt

example (r : ℕ) (P : Fin (r + 1) → Polynomial ℤ) :
    IsPRecursiveSequence r P (fun _ => 0) := by
  intro n hn
  simp

end MetaMathlibExt
