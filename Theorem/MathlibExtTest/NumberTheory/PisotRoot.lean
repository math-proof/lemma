/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PisotRoot.lean -/


import Def.NumberTheory.PisotRoot


namespace MetaMathlibExt

example {P : Polynomial ℝ} {r : ℝ} (h : IsUniquePisotRoot P r) : P.IsRoot r := h.2.1

example {P : Polynomial ℝ} {r s : ℝ} (hr : IsUniquePisotRoot P r)
    (hs : IsPisotNumber s) (hPs : P.IsRoot s) : s = r :=
  hr.2.2 s hs hPs

end MetaMathlibExt
