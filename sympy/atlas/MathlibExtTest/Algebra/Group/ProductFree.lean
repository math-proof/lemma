/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Group/ProductFree.lean -/


import Mathlib.Data.Set.Basic
import sympy.atlas.Algebra.Group.ProductFree

namespace Set

/-- The empty set is product-free. -/
example {M : Type*} [Monoid M] : IsProductFree (∅ : Set M) :=
  fun _ hx _ _ => (Set.notMem_empty _ hx).elim

/-- A product-free set never contains `1`. -/
example {M : Type*} [Monoid M] {S : Set M} (h : IsProductFree S) (h1 : 1 ∈ S) : False :=
  h 1 h1 1 h1 (by simpa using h1)

end Set
