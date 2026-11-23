import Theorem.WeierstrassCurve.TorsionIntegral
import Def.WeierstrassCurve_ReductionMap
import Theorem.WeierstrassCurve.ReductionMap

set_option autoImplicit false

open IsLocalRing


namespace WeierstrassCurve

variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)


section Homomorphism

variable [DecidableEq L] [DecidableEq (ResidueField A)]
variable {W} (hΔ : (W.map (residue A)).Δ ≠ 0)

noncomputable def reduceHom :
    (W.map A.subtype).toAffine.Point →+ (W.map (residue A)).toAffine.Point where
  toFun := reducePoint hΔ
  map_zero' := reducePoint_zero hΔ
  map_add' := reducePoint_add_def hΔ

end Homomorphism

end WeierstrassCurve
