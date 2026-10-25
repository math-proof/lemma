import Mathlib.Algebra.Exact
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Flat.Rank
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Instance.AlgebraicGeometry_FppfCohomologyLES
import Instance.AlgebraicGeometry_FppfGmRepresentable

namespace ModularCurve


namespace AdmissibleInvariants

variable {p : ℕ}

end AdmissibleInvariants

section SixTerm

variable {A B C D E F : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]

end SixTerm

end ModularCurve

set_option autoImplicit false

universe w' w v u

open CategoryTheory Abelian Limits

namespace FppfCohomologyLES

section ChainToDevice

variable {A B C D E F : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]

end ChainToDevice

section FppfPropOneSeven

open AlgebraicGeometry

section WithLocalInstances

variable [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

end WithLocalInstances

end FppfPropOneSeven

end FppfCohomologyLES

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace FppfKummerSES

open CategoryTheory AlgebraicGeometry Limits Opposite Polynomial
open FppfRepresentableGroupSchemeSheaf

section AffineKummerCover

variable (R : CommRingCat.{u}) (u₀ : (R : Type u)ˣ) (p : ℕ)

abbrev kummerPoly : Polynomial (R : Type u) := X ^ p - C (u₀ : (R : Type u))

abbrev KummerAlgebra : Type u := AdjoinRoot (kummerPoly R u₀ p)

end AffineKummerCover

section Epimorphism

variable (p : ℕ)

end Epimorphism

section KummerSES

variable (p : ℕ)

end KummerSES

section ConsumerGates

open FppfCohomologyLES

variable (p : ℕ)

end ConsumerGates

section KernelH0

open FppfCohomologyLES

variable (p : ℕ)

end KernelH0

end FppfKummerSES
