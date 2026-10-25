/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/CategoryTheory/Monoidal/Tor/Additive.lean -/


import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Instance.CategoryTheory.Abelian.LeftDerived.Additive
import Instance.CategoryTheory.Monoidal.Tor.Additive
/-!
# Compile-time checks for additivity of `Tor`

Typeclass inference provides additivity and finite (co)product preservation
for each functor `(Tor C n).obj M`, and additivity of left-derived functors
of additive functors.
-/


namespace CategoryTheory

universe v u

section TorObj

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] [HasProjectiveResolutions C]

example (n : ℕ) (M : C) : Functor.Additive ((Tor C n).obj M) := inferInstance

example (n : ℕ) (M : C) :
    Limits.PreservesFiniteBiproducts ((Tor C n).obj M) := inferInstance

example (n : ℕ) (M : C) :
    Limits.PreservesFiniteProducts ((Tor C n).obj M) := inferInstance

example (n : ℕ) (M : C) :
    Limits.PreservesFiniteCoproducts ((Tor C n).obj M) := inferInstance

end TorObj

section ModuleCatTorObj

variable (R : Type u) [CommRing R]

example (n : ℕ) (M : ModuleCat R) :
    Functor.Additive ((CategoryTheory.Tor (ModuleCat R) n).obj M) :=
  inferInstance

end ModuleCatTorObj

section LeftDerived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]

variable {D : Type*} [Category* D] [Abelian D]

example (F : C ⥤ D) [F.Additive] (n : ℕ) :
    Functor.Additive (F.leftDerived n) := inferInstance

end LeftDerived
end CategoryTheory
