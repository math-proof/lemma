module

public import Mathlib

public section


namespace RealNumbers

/--
[triangle_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/RealNumbers/AbsoluteValue.lean)
-/
public theorem triangle_inequality
  {x y : ℝ} :
-- imply
  |x + y| ≤ |x| + |y| :=
-- proof
  abs_add_le x y

end RealNumbers


-- created on 2026-10-23
