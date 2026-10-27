import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.AffineIsometry.Theorems
open AffineIsometryBuilding DVRContext AnisotropicFormContext


namespace Definitions
end Definitions
namespace AnisotropicFormContext

/--
[embed_two_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometry/Theorems.lean)
-/
@[path]
private lemma embed_two_ne_zero
  {ctx : AnisotropicFormContext} :
-- imply
  ctx.C.embed (1 + 1 : ctx.C.𝔬) ≠ 0 := by
-- proof
  intro h0
  obtain ⟨r, hr_unit, hr_eq⟩ := ctx.two_is_unit
  have : r = 0 := ctx.C.embed_injective (by rw [hr_eq, h0, map_zero])
  subst this; exact not_isUnit_zero hr_unit

end AnisotropicFormContext

namespace AnisotropicFormContext

/--
[form_zero_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometry/Theorems.lean)
-/
@[path]
private lemma form_zero_left
  {ctx : AnisotropicFormContext}
  {w : Fin ctx.C.n → ctx.C.k} :
-- imply
  ctx.form 0 w = 0 := by
-- proof
  have h := ctx.form_smul_left (0 : ctx.C.k) (0 : Fin ctx.C.n → ctx.C.k) w
  simp [zero_mul] at h
  exact h

end AnisotropicFormContext

namespace AnisotropicFormContext

/--
[form_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometry/Theorems.lean)
-/
@[path]
private lemma form_zero_right
  {ctx : AnisotropicFormContext}
  {v : Fin ctx.C.n → ctx.C.k} :
-- imply
  ctx.form v 0 = 0 := by
-- proof
  rw [ctx.form_symm]; exact ctx.form_zero_left v

end AnisotropicFormContext

namespace AnisotropicFormContext

/--
[form_zero_isInO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometry/Theorems.lean)
-/
@[path]
private lemma form_zero_isInO
  {ctx : AnisotropicFormContext} :
-- imply
  ctx.C.isInO (ctx.form (0 : Fin ctx.C.n → ctx.C.k) (0 : Fin ctx.C.n → ctx.C.k)) := by
-- proof
  rw [ctx.form_zero_left]; exact ctx.isInO_zero

end AnisotropicFormContext

namespace AnisotropicFormContext

/--
[isInO_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometry/Theorems.lean)
-/
@[path]
private lemma isInO_sub
  {ctx : AnisotropicFormContext}
  {x y : ctx.C.k}
-- given
  (hx : ctx.C.isInO x)
  (hy : ctx.C.isInO y) :
-- imply
  ctx.C.isInO (x - y) := by
-- proof
  rw [sub_eq_add_neg]; exact ctx.isInO_add hx (ctx.isInO_neg hy)

end AnisotropicFormContext

namespace AnisotropicFormContext

/--
[form_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometry/Theorems.lean)
-/
@[path]
private lemma form_add_right
  {ctx : AnisotropicFormContext}
  {v w₁ w₂ : Fin ctx.C.n → ctx.C.k} :
-- imply
  ctx.form v (w₁ + w₂) = ctx.form v w₁ + ctx.form v w₂ := by
-- proof
  rw [ctx.form_symm v (w₁ + w₂), ctx.form_add_left, ctx.form_symm w₁ v, ctx.form_symm w₂ v]

end AnisotropicFormContext

namespace AnisotropicFormContext

/--
[form_smul_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometry/Theorems.lean)
-/
@[path]
private lemma form_smul_right
  {ctx : AnisotropicFormContext}
  {c : ctx.C.k}
  {v w : Fin ctx.C.n → ctx.C.k} :
-- imply
  ctx.form v (c • w) = c * ctx.form v w := by
-- proof
  rw [ctx.form_symm v (c • w), ctx.form_smul_left, ctx.form_symm w v]

end AnisotropicFormContext

namespace AnisotropicFormContext

/--
[smul_selfpair_isInO](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometry/Theorems.lean)
-/
@[path]
private lemma smul_selfpair_isInO
  {ctx : AnisotropicFormContext}
  {c : ctx.C.k}
  {v : Fin ctx.C.n → ctx.C.k}
-- given
  (hc : ctx.C.isInO c)
  (hv : ctx.C.isInO (ctx.form v v)) :
-- imply
  ctx.C.isInO (ctx.form (c • v) (c • v)) := by
-- proof
  rw [ctx.form_smul_left, ctx.form_smul_right]
  exact ctx.isInO_mul hc (ctx.isInO_mul hc hv)

end AnisotropicFormContext

namespace AnisotropicFormContext

/--
[closed_under_o_combination_data](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometry/Theorems.lean)
-/
@[path]
private lemma closed_under_o_combination_data
  {ctx : AnisotropicFormContext}
  {coeffs : Fin ctx.C.n → ctx.C.k}
  {vectors : Fin ctx.C.n → (Fin ctx.C.n → ctx.C.k)}
-- given
  (hcoeffs : ∀ i, ctx.C.isInO (coeffs i))
  (hvecs : ∀ i, ctx.C.isInO (ctx.form (vectors i) (vectors i))) :
-- imply
  ctx.C.isInO (ctx.form (∑ i, coeffs i • vectors i) (∑ i, coeffs i • vectors i)) := by
-- proof
  have : ∀ (s : Finset (Fin ctx.C.n)),
    ctx.C.isInO (ctx.form (∑ i ∈ s, coeffs i • vectors i)
      (∑ i ∈ s, coeffs i • vectors i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ctx.form_zero_isInO
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact ctx.selfpair_add_closed _ _
        (ctx.smul_selfpair_isInO _ _ (hcoeffs _) (hvecs _)) ih
  exact this Finset.univ

end AnisotropicFormContext

namespace AnisotropicFormContext

/--
[maxLat_complete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometry/Theorems.lean)
-/
@[path]
private lemma maxLat_complete
  {ctx : AnisotropicFormContext} :
-- imply
  ∀ v : Fin ctx.C.n → ctx.C.k, ctx.C.isInO (ctx.form v v) → v ∈ ctx.maxLat.carrier :=
-- proof
  fun _v hv => hv

end AnisotropicFormContext

namespace AnisotropicFormContext

/--
[maxLat_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometry/Theorems.lean)
-/
@[path]
private lemma maxLat_integral
  {ctx : AnisotropicFormContext} :
-- imply
  ∀ v ∈ ctx.maxLat.carrier, ∀ w ∈ ctx.maxLat.carrier, ctx.C.isInO (ctx.form v w) := by
-- proof
  intro v hv w hw
  have hvw_sum : ctx.C.isInO (ctx.form (v + w) (v + w)) :=
    ctx.selfpair_add_closed v w hv hw
  have expand : ctx.form (v + w) (v + w) =
    ctx.form v v + ctx.form v w + ctx.form w v + ctx.form w w := by
    rw [ctx.form_add_left v w (v + w)]
    rw [ctx.form_symm v (v + w), ctx.form_add_left v w v,
      ctx.form_symm v v, ctx.form_symm w v]
    rw [ctx.form_symm w (v + w), ctx.form_add_left v w w,
      ctx.form_symm v w, ctx.form_symm w w]
    ring
  have symm_vw : ctx.form w v = ctx.form v w := ctx.form_symm w v
  have h_two_vw : ctx.form v w + ctx.form v w =
    ctx.form (v + w) (v + w) - ctx.form v v - ctx.form w w := by
    rw [expand, symm_vw]; ring
  have h_two_vw_inO : ctx.C.isInO (ctx.form v w + ctx.form v w) := by
    rw [h_two_vw]
    exact ctx.isInO_sub (ctx.isInO_sub hvw_sum hv) hw
  have h2_eq : ctx.form v w + ctx.form v w = ctx.C.embed (1 + 1 : ctx.C.𝔬) * ctx.form v w := by
    simp [map_add, map_one]; ring
  rw [h2_eq] at h_two_vw_inO
  have h2_ne : ctx.C.embed (1 + 1 : ctx.C.𝔬) ≠ 0 := ctx.embed_two_ne_zero
  have h_rewrite : ctx.form v w =
    (ctx.C.embed (1 + 1 : ctx.C.𝔬))⁻¹ * (ctx.C.embed (1 + 1 : ctx.C.𝔬) * ctx.form v w) := by
    rw [← mul_assoc, inv_mul_cancel₀ h2_ne, one_mul]
  rw [h_rewrite]
  exact ctx.isInO_mul (ctx.isUnitInO_inv ctx.two_is_unit) h_two_vw_inO

end AnisotropicFormContext


-- created on 2026-10-24
