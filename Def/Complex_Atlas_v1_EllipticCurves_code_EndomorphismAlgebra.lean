import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.EllipticCurves.code.EndomorphismAlgebra.Part2

open NumberField Module ConductorOrder
open scoped Quaternion
open Module
open TensorProduct
open WeierstrassCurve.Affine


/--
[ringOfIntegers_isOrder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
universe u
namespace ConductorOrder
variable {d : ℤ}

namespace ConductorOrder

/--
[mem_conductorOrder_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
end ConductorOrder

namespace ConductorOrder

/--
[conductorOrder_le_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
end ConductorOrder

namespace ConductorOrder

/--
[conductorOrder_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
end ConductorOrder

namespace ConductorOrder

/--
[intCast_mem_subring](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
end ConductorOrder

namespace ConductorOrder

/--
[mem_subring_of_dvd_im](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
end ConductorOrder

namespace ConductorOrder

/--
[conductorOrder_isOrder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
end ConductorOrder

namespace ConductorOrder

/--
[exists_conductor_of_subring](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
end ConductorOrder

namespace ConductorOrder

/--
[orders_eq_conductorOrders](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
end ConductorOrder

/--
[qI_mul_qI](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
@[reducible] noncomputable def toDivisionRing {k : Type*} [Field k] (a b : k)
  (h : ∀ γ : ℍ[k, a, b], reducedNorm a b γ = 0 → γ = 0) :
  DivisionRing ℍ[k, a, b] :=
  DivisionRing.ofIsUnitOrEqZero (fun γ => by
    by_cases hγ : γ = 0
    · right; exact hγ
    · left; exact (isDivisionRing_iff_norm_anisotropic a b).mp h γ hγ)
section Lemma125
open TensorProduct

/--
[algebraMap_mul_eq_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismAlgebra.lean)
-/
end Lemma125
section Corollary1220
open WeierstrassCurve.Affine
universe v
variable {F : Type v} [Field F] [DecidableEq F]
variable (E : WeierstrassCurve.Affine F)
/-- The subring of "isogeny endomorphisms" of `E` inside the full endomorphism ring;
this is the subring relevant for Corollary 12.20. -/
end Corollary1220
section Definition1221
open WeierstrassCurve.Affine
universe w
variable {F : Type w} [Field F] [DecidableEq F]
/-- Definition 12.21: an elliptic curve `E` has complex multiplication if
`End(E) ≇ ℤ`. -/
end Definition1221


-- created on 2026-10-23
