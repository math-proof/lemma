import Structure.AlgebraicCurve_LocalResidue
import Mathlib.RingTheory.Trace.Basic

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

class HasLocalResidue : Prop where
  exists_data : ∀ v : Place K F, Nonempty v.LocalResidueData

class HasCanonicalLocalResidueK : Prop where
  exists_data : ∀ v : Place K F, Nonempty v.CanonicalLocalResidueDataK

class HasCanonicalLocalResidueKStar where
  dataKStar : ∀ v : Place K F, v.CanonicalLocalResidueDataK

class HasSeparableResidue : Prop where
  trace_ne_zero : ∀ v : Place K F, (Algebra.trace K v.ResidueField : _ →ₗ[K] K) ≠ 0

end AlgebraicCurve
