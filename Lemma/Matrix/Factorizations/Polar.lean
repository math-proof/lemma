import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped ComplexOrder


namespace Matrix

/--
[exists_unitaryGroup_posSemidef](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Factorizations/Polar.lean)
-/
@[path]
lemma exists_unitaryGroup_posSemidef
  [Fintype n] [DecidableEq n]
  {A : Matrix n n ℂ} :
-- imply
  ∃ (U : Matrix.unitaryGroup n ℂ) (P : Matrix n n ℂ),
    P.PosSemidef ∧ P * P = Aᴴ * A ∧ A = (U : Matrix n n ℂ) * P := by
-- proof
  obtain ⟨U, V, σ, hσ, hA⟩ := exists_unitaryGroup_diagonal_nonneg A
  set D : Matrix n n ℂ := diagonal fun i => (σ i : ℂ)
  have hD : D.PosSemidef := PosSemidef.diagonal fun i => Complex.zero_le_real.2 (hσ i)
  have hDs : star D = D := by
    simp [D, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  have hU : ∀ X : Matrix n n ℂ, star (U : Matrix n n ℂ) * (U * X) = X := fun X => by
    rw [← mul_assoc, Matrix.mem_unitaryGroup_iff'.1 U.2, one_mul]
  have hV : ∀ X : Matrix n n ℂ, star (V : Matrix n n ℂ) * (V * X) = X := fun X => by
    rw [← mul_assoc, Matrix.mem_unitaryGroup_iff'.1 V.2, one_mul]
  refine ⟨U * star V, V * D * star (V : Matrix n n ℂ), ?_, ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using hD.mul_mul_conjTranspose_same (V : Matrix n n ℂ)
  · rw [hA, ← Matrix.star_eq_conjTranspose]
    simp only [star_mul, star_star, hDs, mul_assoc, hU, hV]
  · rw [hA, Submonoid.coe_mul, Unitary.coe_star]
    simp only [mul_assoc, hV]
end Matrix
namespace Matrix

end Matrix

namespace Matrix

variable [Fintype n]
variable {𝕜 : Type*} [RCLike 𝕜]
/--
[polar_posDef_conjTranspose_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Factorizations/Polar.lean)
-/
@[path]
private lemma polar_posDef_conjTranspose_mul_self [DecidableEq n] (A : Matrix n n 𝕜)
  (hA : IsUnit A.det) : (Aᴴ * A).PosDef :=
  PosDef.conjTranspose_mul_self A <|
    mulVec_injective_iff_isUnit.mpr <| (isUnit_iff_isUnit_det A).mpr hA

end Matrix

namespace Matrix

variable [Fintype n]
variable {𝕜 : Type*} [RCLike 𝕜]
/--
[polar_posDef_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Factorizations/Polar.lean)
-/
@[path]
open scoped MatrixOrder Classical in
private lemma polar_posDef_sqrt {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
  (CFC.sqrt Q).PosDef :=
isStrictlyPositive_iff_posDef.mp hQ.isStrictlyPositive.sqrt

end Matrix

namespace Matrix

variable [Fintype n]
variable {𝕜 : Type*} [RCLike 𝕜]
/--
[polar_sqrt_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Factorizations/Polar.lean)
-/
@[path]
open scoped MatrixOrder Classical in
private lemma polar_sqrt_mul_self {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
  CFC.sqrt Q * CFC.sqrt Q = Q :=
  CFC.sqrt_mul_sqrt_self Q hQ.posSemidef.nonneg

end Matrix

namespace Matrix

variable [Fintype n]
variable {𝕜 : Type*} [RCLike 𝕜]
/--
[polar_mul_inv_mem_unitaryGroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Factorizations/Polar.lean)
-/
@[path]
private lemma polar_mul_inv_mem_unitaryGroup [DecidableEq n]
  {A P : Matrix n n 𝕜} (hP : P.PosDef) (hsq : P * P = Aᴴ * A) :
  A * P⁻¹ ∈ unitaryGroup n 𝕜 := by
  rw [mem_unitaryGroup_iff']
  simp only [star_mul, star_eq_conjTranspose, conjTranspose_nonsing_inv,
    hP.isHermitian.eq]
  have hPdet : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP.isUnit
  calc
    (P⁻¹ * Aᴴ) * (A * P⁻¹) = P⁻¹ * (Aᴴ * A) * P⁻¹ := by simp only [mul_assoc]
    _ = P⁻¹ * (P * P) * P⁻¹ := by rw [← hsq]
    _ = (P⁻¹ * P) * (P * P⁻¹) := by simp only [mul_assoc]
    _ = 1 := by rw [nonsing_inv_mul P hPdet, mul_nonsing_inv P hPdet, one_mul]

end Matrix

namespace Matrix

variable [Fintype n]
variable {𝕜 : Type*} [RCLike 𝕜]
/--
[polar_eq_sqrt_of_posDef_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Factorizations/Polar.lean)
-/
@[path]
open scoped MatrixOrder Classical in
private lemma polar_eq_sqrt_of_posDef_sq {P Q : Matrix n n 𝕜} (hP : P.PosDef)
  (hsq : P * P = Q) : P = CFC.sqrt Q :=
  (CFC.sqrt_unique hsq hP.posSemidef.nonneg).symm

end Matrix

namespace Matrix

variable [Fintype n]
variable {𝕜 : Type*} [RCLike 𝕜]
/--
[polar_mul_inv_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Factorizations/Polar.lean)
-/
@[path]
private lemma polar_mul_inv_mul [DecidableEq n] {A P : Matrix n n 𝕜} (hP : P.PosDef) :
  A = (A * P⁻¹) * P := by
  have hPdet : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP.isUnit
  calc
    A = A * 1 := (mul_one A).symm
    _ = A * (P⁻¹ * P) := by rw [nonsing_inv_mul P hPdet]
    _ = (A * P⁻¹) * P := (mul_assoc _ _ _).symm

end Matrix

namespace Matrix

variable [Fintype n]
variable {𝕜 : Type*} [RCLike 𝕜]
/--
[polar_sq_eq_conjTranspose_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Factorizations/Polar.lean)
-/
@[path]
private lemma polar_sq_eq_conjTranspose_mul_self [DecidableEq n]
  {A U P : Matrix n n 𝕜} (hU : U ∈ unitaryGroup n 𝕜) (hP : P.PosDef)
  (hA : A = U * P) : P * P = Aᴴ * A := by
  have hUconj : Uᴴ * U = 1 := by
    simpa only [star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp hU
  calc
    P * P = P * (Uᴴ * U) * P := by rw [hUconj, mul_one]
    _ = (U * P)ᴴ * (U * P) := by
      rw [conjTranspose_mul, hP.isHermitian.eq]
      simp only [mul_assoc]
    _ = Aᴴ * A := by rw [← hA]

end Matrix

namespace Matrix

/--
[exists_unique_unitaryGroup_posDef_of_isUnit_det](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Factorizations/Polar.lean)
-/
@[path]
lemma exists_unique_unitaryGroup_posDef_of_isUnit_det
  [Fintype n] [RCLike 𝕜] [DecidableEq n]
  {A : Matrix n n 𝕜}
-- given
  (hA : IsUnit A.det) :
-- imply
  ∃ (U : Matrix.unitaryGroup n 𝕜) (P : Matrix n n 𝕜),
    P.PosDef ∧ A = (U : Matrix n n 𝕜) * P ∧
    ∀ (U' : Matrix.unitaryGroup n 𝕜) (P' : Matrix n n 𝕜),
    P'.PosDef → A = (U' : Matrix n n 𝕜) * P' → U' = U ∧ P' = P := by
-- proof
  let Q := Aᴴ * A
  let P := CFC.sqrt Q
  let U := A * P⁻¹
  have hQ : Q.PosDef := by
    simpa only [Q] using polar_posDef_conjTranspose_mul_self A hA
  have hP : P.PosDef := by
    simpa only [P] using polar_posDef_sqrt hQ
  have hPsq : P * P = Aᴴ * A := by
    simpa only [P, Q] using polar_sqrt_mul_self hQ
  have hU : U ∈ unitaryGroup n 𝕜 := by
    simpa only [U] using polar_mul_inv_mem_unitaryGroup hP hPsq
  have hdecomp : A = U * P := by
    simpa only [U] using polar_mul_inv_mul hP
  refine ⟨⟨U, hU⟩, P, hP, hdecomp, ?_⟩
  intro U' P' hP' hdecomp'
  have hP'eq : P' = P := by
    apply polar_eq_sqrt_of_posDef_sq hP'
    simpa only [P, Q] using
      polar_sq_eq_conjTranspose_mul_self U'.property hP' hdecomp'
  have hU'eq : (U' : Matrix n n 𝕜) = U := by
    apply hP.isUnit.mul_right_cancel
    calc
      (U' : Matrix n n 𝕜) * P = U' * P' := by rw [hP'eq]
      _ = A := hdecomp'.symm
      _ = U * P := hdecomp
  exact ⟨Subtype.ext hU'eq, hP'eq⟩

end Matrix


-- created on 2026-10-20
-- updated on 2026-10-26
