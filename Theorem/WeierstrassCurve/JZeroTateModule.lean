module

public import Theorem.LaurentSeries.ArithmeticGalois
public import Def.HeckeGalois_EichlerShimura
public import Theorem.WeierstrassCurve.TateModule
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.Basis.Defs
public import Abbrev.ModularCurve_JZeroTateModule

public noncomputable section

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace ModularCurve

section Integral

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]


public theorem tateHeckeRep_apply (t : HeckeAlg) :
    tateHeckeRep p J t = TateModule.rep p J HeckeAlg t :=
  rfl


public theorem coe_tateHeckeRep_apply_apply (t : HeckeAlg) (x : TateModule p J) (n : ℕ) :
    ((tateHeckeRep p J t x : TateModule p J) : ℕ → J) n = t • (x : ℕ → J) n :=
  rfl

end Integral

section Rational

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J]


public theorem rationalGaloisRep_apply (G : Type) [Monoid G] [DistribMulAction G J] (g : G) :
    rationalGaloisRep p J G g = (TateModule.rep p J G g).baseChange ℚ_[p] :=
  rfl


public theorem rationalGaloisRep_tmul (G : Type) [Monoid G] [DistribMulAction G J] (g : G) (a : ℚ_[p])
    (x : TateModule p J) :
    rationalGaloisRep p J G g (a ⊗ₜ x) = a ⊗ₜ TateModule.rep p J G g x :=
  rfl

variable [Module HeckeAlg J]


public theorem rationalHeckeRep_apply (t : HeckeAlg) :
    rationalHeckeRep p J t = (tateHeckeRep p J t).baseChange ℚ_[p] :=
  rfl


public theorem rationalHeckeRep_tmul (t : HeckeAlg) (a : ℚ_[p]) (x : TateModule p J) :
    rationalHeckeRep p J t (a ⊗ₜ x) = a ⊗ₜ tateHeckeRep p J t x :=
  rfl


public theorem rationalHeckeRep_mem_rationalHeckeAlgebra (t : HeckeAlg) :
    rationalHeckeRep p J t ∈ rationalHeckeAlgebra p J :=
  Algebra.subset_adjoin (Set.mem_range_self t)

end Rational

section Predicate

variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]

