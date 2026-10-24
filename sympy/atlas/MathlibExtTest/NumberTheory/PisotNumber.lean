/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PisotNumber.lean -/


import sympy.atlas.NumberTheory.PisotNumber

namespace MetaMathlibExt

example {q : ℝ} (hq : IsPisotNumber q) : IsIntegral ℤ q := hq.1
example {q : ℝ} (hq : IsPisotNumber q) : 1 < q := hq.2.1

end MetaMathlibExt
