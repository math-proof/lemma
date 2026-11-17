/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PisotNumber.lean -/
module

public import Def.NumberTheory.PisotNumber

public section

namespace MetaMathlibExt

example {q : ℝ} (hq : IsPisotNumber q) : IsIntegral ℤ q := hq.1

example {q : ℝ} (hq : IsPisotNumber q) : 1 < q := hq.2.1

end MetaMathlibExt
