import Class.AlgebraicCurve_DivisorClassGroup
import Mathlib.RingTheory.Kaehler.Basic

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

class IsCurveOver : Prop extends HasPrincipalDivisors K F where
  finiteResidue : ∀ v : Place K F, Module.Finite K v.ResidueField
  kaehler_free_rank_one : Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1

end AlgebraicCurve
