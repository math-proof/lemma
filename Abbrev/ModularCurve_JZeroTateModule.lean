module
public import Instance.ModularCurve_ArithmeticGalois
public import Structure.HeckeGalois_EichlerShimura
public import Instance.EllipticCurve_TateModule
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.Basis.Defs
set_option autoImplicit false


public section

noncomputable section

open scoped TensorProduct

namespace ModularCurve

section Integral

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]

end Integral

section Rational

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J]

abbrev RationalTateModule : Type :=
  ℚ_[p] ⊗[ℤ_[p]] TateModule p J

end Rational

section Predicate

variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]

end Predicate

section ModularInstance

end ModularInstance

end ModularCurve

end
