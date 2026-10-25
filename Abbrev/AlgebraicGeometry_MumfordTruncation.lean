import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.Module.Projective

set_option autoImplicit false

noncomputable section

universe u v w w'

namespace TwoChartCech

namespace KerCoprod

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable {P : Type w'} [AddCommGroup P] [Module R P]
variable (d : C0 →ₗ[R] C1) (g : P →ₗ[R] C1)

abbrev K0 : Submodule R (C0 × P) := LinearMap.ker (d.coprod g)

end KerCoprod

namespace Mumford

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]

end Mumford

section Gates

end Gates

end TwoChartCech

end
