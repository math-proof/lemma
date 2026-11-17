module

public import Mathlib
public import Def.NumberTheory.NormalNumber

public section

open Real Filter
open MetaMathlibExt.NormalNumber


namespace MetaMathlibExt.NormalNumber

/--
[IsNormalInBase.isSimplyNormalInBase](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NormalNumber.lean)
-/
public theorem IsNormalInBase.isSimplyNormalInBase
  {b : ℕ}
  {x : ℝ}
-- given
  (h : IsNormalInBase b x) :
-- imply
  IsSimplyNormalInBase b x := by
-- proof
  intro d hd
  simpa [Fin.forall_fin_one] using h 1 (fun _ => d) (fun _ => hd)

end MetaMathlibExt.NormalNumber


-- created on 2026-10-20
-- updated on 2026-10-26
