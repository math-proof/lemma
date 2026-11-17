module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Abbrev.Analysis.InnerProductSpace.EuclideanVec
public import Def.Analysis.Normed.Lp.LpSpace

public section

namespace LpSpace

variable {p d : ℕ}

@[simp]
theorem toL2_ofL2 (x : EuclideanVec d) : (ofL2 p x).toL2 = x := rfl

@[simp]
theorem ofL2_toL2 (x : LpSpace p d) : ofL2 p x.toL2 = x := rfl

end LpSpace
