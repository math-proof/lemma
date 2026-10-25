import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraNotes.code.ProductGroups
open ProductGroups


namespace Definitions
end Definitions
namespace ProductGroups

/--
[prod_group_mul_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/ProductGroups.lean)
-/
@[path]
private lemma prod_group_mul_def
  [Group G]
  [Group H]
  {g₁ g₂ : G}
-- given
  (h₀ h₁ : H) :
-- imply
  (g₁, h₀) * (g₂, h₁) = (g₁ * g₂, h₀ * h₁) := by
-- proof
  rfl

end ProductGroups


-- created on 2026-10-24
