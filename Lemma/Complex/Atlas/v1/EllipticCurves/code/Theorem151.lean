import Mathlib
import Initialize.Tactic.Attr.Basic
import Class.v1.Atlas.EllipticCurves.code.Theorem151
open Complex ComplexLattice


namespace ComplexLattice

variable (L : ComplexLattice)
/--
[ellipticCurveEL_Δ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem151.lean)
-/
@[path]
discriminant `Δ(L) = g₂³ - 27 g₃²` (up to the normalization built into
`discriminantLattice`). -/
lemma ellipticCurveEL_Δ_eq : L.ellipticCurveEL_affine.Δ = L.discriminantLattice := by
  unfold discriminantLattice ellipticCurveEL_affine ellipticCurveEL WeierstrassCurve.toAffine
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

end ComplexLattice

namespace ComplexLattice

variable (L : ComplexLattice)
/--
[ellipticCurveEL_Δ_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem151.lean)
-/
@[path]
(this is Lemma 14.33 applied to `E_L`). -/
lemma ellipticCurveEL_Δ_ne_zero : L.ellipticCurveEL_affine.Δ ≠ 0 := by
  rwa [L.ellipticCurveEL_Δ_eq]

end ComplexLattice

namespace ComplexLattice

/--
[weierstrassP_point_equation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem151.lean)
-/
@[path]
lemma weierstrassP_point_equation
  {L : ComplexLattice}
  {z : ℂ}
-- given
  (hz : z ∉ (L.lattice : Set ℂ)) :
-- imply
  L.ellipticCurveEL_affine.Equation (L.weierstrassPFun z) (L.derivWeierstrassPFun z / 2) := by
-- proof
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [ellipticCurveEL_affine, ellipticCurveEL, WeierstrassCurve.toAffine]
  have h := L.weierstrassPFun_differentialEquation z hz
  simp only [g₂Fun_eq, g₃Fun_eq] at h
  simp only [zero_mul, add_zero]
  rw [div_pow, h]
  field_simp
  ring

end ComplexLattice

namespace ComplexLattice

/--
[weierstrassP_point_nonsingular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem151.lean)
-/
@[path]
lemma weierstrassP_point_nonsingular
  {L : ComplexLattice}
  {z : ℂ}
-- given
  (hz : z ∉ (L.lattice : Set ℂ)) :
-- imply
  L.ellipticCurveEL_affine.Nonsingular (L.weierstrassPFun z) (L.derivWeierstrassPFun z / 2) := by
-- proof
  exact (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (L.ellipticCurveEL_Δ_ne_zero)).mp (L.weierstrassP_point_equation z hz)

end ComplexLattice

namespace ComplexLattice

/--
[PhiLift_add_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem151.lean)
-/
@[path]
lemma PhiLift_add_lattice
  {L : ComplexLattice}
  {z ω : ℂ}
-- given
  (hω : ω ∈ L.lattice) :
-- imply
  L.PhiLift (z + ω) = L.PhiLift z := by
-- proof
  classical
  unfold PhiLift
  by_cases hz : z ∈ (L.lattice : Set ℂ)
  ·
    have hzw : z + ω ∈ (L.lattice : Set ℂ) :=
      L.lattice.add_mem hz hω
    simp [hzw, hz]
  ·
    by_cases hzw : z + ω ∈ (L.lattice : Set ℂ)
    ·
      exfalso
      apply hz
      have : z = (z + ω) - ω := by ring
      rw [this]
      exact L.lattice.sub_mem hzw hω
    · simp only [hzw, hz, dite_false]
      unfold PhiAux
      congr 1
      · exact L.weierstrassPFun_add_lattice z ω hω
      · rw [L.derivWeierstrassPFun_add_lattice z ω hω]

end ComplexLattice

namespace ComplexLattice

/--
[PhiFun_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem151.lean)
-/
@[path]
lemma PhiFun_zero
  {L : ComplexLattice} :
-- imply
  L.PhiFun 0 = 0 := by
-- proof
  classical
  show L.PhiLift 0 = 0
  unfold PhiLift
  have h0 : (0 : ℂ) ∈ (L.lattice : Set ℂ) := L.lattice.zero_mem
  simp [h0]

end ComplexLattice

namespace ComplexLattice

/--
[PhiFun_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem151.lean)
-/
@[path]
lemma PhiFun_mk
  {L : ComplexLattice}
  {z : ℂ}
-- given
  (hz : z ∉ (L.lattice : Set ℂ)) :
-- imply
  L.PhiFun (QuotientAddGroup.mk z) = L.PhiAux z hz := by
-- proof
  classical
  show L.PhiLift z = L.PhiAux z hz
  unfold PhiLift
  simp [hz]

end ComplexLattice

/--
[ellipticCurveEL_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem151.lean)
-/
@[path]
private lemma ellipticCurveEL__eq
  {L : ComplexLattice} :
-- imply
  L.ellipticCurveEL_affine.Δ = L.discriminantLattice := by
-- proof
  apply ComplexLattice.ellipticCurveEL_ L

/--
[ellipticCurveEL_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem151.lean)
-/
@[path]
private lemma ellipticCurveEL__eq_2
  {L : ComplexLattice} :
-- imply
  L.ellipticCurveEL_affine.Δ ≠ 0 := by
-- proof
  apply ComplexLattice.ellipticCurveEL_ L


-- created on 2026-10-23
