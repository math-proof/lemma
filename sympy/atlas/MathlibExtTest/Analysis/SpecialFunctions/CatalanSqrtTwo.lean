/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/CatalanSqrtTwo.lean -/


import sympy.atlas.Analysis.SpecialFunctions.CatalanSqrtTwo

open scoped Topology
open Filter

namespace MathlibExtTest.Analysis.SpecialFunctions.CatalanSqrtTwo

open MathlibExt.Analysis.SpecialFunctions.CatalanSqrtTwo

/-- The Catalan product terms are multipliable, derived from the public `HasProd`. -/
example : Multipliable (fun m : Nat =>
    (((4 * m + 2 : Nat) : Real) ^ 2) /
      (((4 * m + 1 : Nat) : Real) * ((4 * m + 3 : Nat) : Real))) :=
  catalan_hasProd_sqrt_two.multipliable

/-- Natural partial products converge to `√2`, derived from the public `HasProd`. -/
example : Tendsto (fun N => ∏ m ∈ Finset.range N,
      ((((4 * m + 2 : Nat) : Real) ^ 2) /
        (((4 * m + 1 : Nat) : Real) * ((4 * m + 3 : Nat) : Real)))) atTop
      (𝓝 (Real.sqrt 2)) :=
  catalan_hasProd_sqrt_two.tendsto_prod_nat

/-- The infinite product equals `√2`, derived from the public `HasProd`. -/
example : ∏' m : Nat,
      ((((4 * m + 2 : Nat) : Real) ^ 2) /
        (((4 * m + 1 : Nat) : Real) * ((4 * m + 3 : Nat) : Real))) =
      Real.sqrt 2 :=
  catalan_hasProd_sqrt_two.tprod_eq

end MathlibExtTest.Analysis.SpecialFunctions.CatalanSqrtTwo
