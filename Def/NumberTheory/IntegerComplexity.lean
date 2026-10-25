/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean -/

import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Find
import Inductive.NumberTheory.IntegerComplexity


namespace IntegerComplexity

namespace Expr

/-- Natural evaluation. Source C2. -/
def eval : Expr → ℕ
  | .one => 1
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval

/-- Number of ones (leaf count). Source C3. -/
def count : Expr → ℕ
  | .one => 1
  | .add a b => a.count + b.count
  | .mul a b => a.count + b.count

end Expr
end IntegerComplexity
