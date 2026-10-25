import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Structure.AlgebraicCurve_CurveModel
import Instance.JacJ1_ChartAlgebra
import Instance.AlgebraicCurve_CurveModelSmooth

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IntermediateField IsDedekindDomain
open Topology TopCat

universe u

namespace AlgebraicCurve

namespace CurveModel

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)

section Charts

abbrev X₀ : Scheme.{u} := Spec (CommRingCat.of (chartRing K ({t} : Set L)))

abbrev XInf : Scheme.{u} := Spec (CommRingCat.of (chartRing K ({t⁻¹} : Set L)))

abbrev XOverlap : Scheme.{u} := Spec (CommRingCat.of (chartRing K ({t, t⁻¹} : Set L)))

end Charts

section Glue

variable [Fact (t ≠ 0)]

end Glue

section Qualities

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

end Qualities

section FiniteType

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

end FiniteType

section Overlap

variable [Fact (t ≠ 0)]

end Overlap

section StalkRange

variable [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]


end StalkRange

section PlaceMap

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

end PlaceMap

open IsLocalRing

section Compact

variable [Fact (t ≠ 0)]

end Compact

section Noetherian

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

end Noetherian

section RingLemmas

variable {B R F : Type*} [CommRing B] [CommRing R] [CommRing F]

end RingLemmas

section SpecLemmas

end SpecLemmas

section LiftLemma

variable [Fact (t ≠ 0)]

end LiftLemma

section Generic

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

end Generic

section Closed

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]


end Closed

section ClosedLift

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

end ClosedLift

section Uniqueness

variable [Fact (t ≠ 0)]

end Uniqueness

section Proper

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

end Proper

open TopologicalSpace

section ChartGerms

variable (A : Subalgebra K L)

end ChartGerms

section LocalSections

variable (a : K)

end LocalSections

section Values

variable [Fact (t ≠ 0)] (a : K)

end Values

section Affine

variable [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] (a : K) (ha : (t - algebraMap K L a) ≠ 0)

end Affine

section Packaging

variable [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]

end Packaging

section TowerPack

variable [Algebra (RatFunc K) L] [IsScalarTower K (RatFunc K) L]

end TowerPack

end CurveModel

end AlgebraicCurve

end
