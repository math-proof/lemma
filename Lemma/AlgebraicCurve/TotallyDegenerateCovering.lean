import Lemma.AlgebraicCurve.SemistableCharts
import Def.CerednikDrinfeld_Ribbon
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Structure.AlgebraicCurve_TotallyDegenerateCovering

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing CerednikDrinfeld

variable {L : Type} [Field L] (A : ValuationSubring L) (F : Type) [Field F] [Algebra L F]


namespace TotallyDegenerateCovering

variable {A F} {ϖ : A} (𝒞 : TotallyDegenerateCovering A F ϖ)

def toDegeneracyData : DegeneracyData 𝒞.E 𝒞.V where
  a := 𝒞.src
  b := 𝒞.tgt
  w := 𝒞.width

@[simp] theorem toDegeneracyData_a (e : 𝒞.E) : 𝒞.toDegeneracyData.a e = 𝒞.src e := rfl
@[simp] theorem toDegeneracyData_b (e : 𝒞.E) : 𝒞.toDegeneracyData.b e = 𝒞.tgt e := rfl
@[simp] theorem toDegeneracyData_w (e : 𝒞.E) : 𝒞.toDegeneracyData.w e = 𝒞.width e := rfl

protected theorem src_ne_tgt (e : 𝒞.E) : 𝒞.src e ≠ 𝒞.tgt e := fun h => by
  have h0 := 𝒞.side_src e
  rw [h, 𝒞.side_tgt e] at h0
  exact one_ne_zero h0

end TotallyDegenerateCovering

end AlgebraicCurve

end
