/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/CategoryTheory/Monoidal/Tor/Additive.lean -/

import Mathlib.CategoryTheory.Monoidal.Tor
import sympy.atlas.CategoryTheory.Abelian.LeftDerived.Additive
/-!
# Additivity of `Tor`

For a monoidal abelian preadditive category with projective resolutions,
`Tor C n` left-derives the tensor product in the second variable. Since
tensoring with a fixed object is additive and left-derived functors of additive
functors are additive, each functor `(Tor C n).obj M` is additive.
-/

namespace CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] [HasProjectiveResolutions C]

/-- Each functor `(Tor C n).obj M` is additive. -/
instance Tor.obj_additive (n : ℕ) (M : C) :
    Functor.Additive ((Tor C n).obj M) := by
  dsimp [Tor]
  infer_instance

end CategoryTheory
