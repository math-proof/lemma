import Mathlib
import Lemma.Definitions.Def_TateCurve_XMultIdentities

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Filter
open WeierstrassCurve.Affine

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

section PsiTwo

variable [CompleteSpace K] {q w : K}

variable (q w) in

noncomputable def pointPsiTwo : K := 2 * pointY q w + pointX q w

end PsiTwo

section Defect

variable [CompleteSpace K] {q u v : K}

variable (q u v)

noncomputable def addDefectDiff : K :=
  (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 +
    pointPsiTwo q u * pointPsiTwo q v


end Defect

end TateCurve
set_option linter.unusedSectionVars false

open WeierstrassCurve.Affine

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u v w ζ : K} {p : ℕ}

variable (q) in

def DiffHyp : Prop :=
  ∀ u v : K, AddParams q u v →
    (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v))

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Region

variable {q u v : K}

structure ExpansionRegion (q u v : K) : Prop where
  params : AddParams q u v
  norm_q_lt_one : ‖q‖ < 1
  u_lo : ‖q‖ < ‖u‖
  u_hi : ‖q‖ * ‖u‖ < 1
  v_lo : ‖q‖ < ‖v‖
  v_hi : ‖q‖ * ‖v‖ < 1
  mul_lo : ‖q‖ < ‖u * v‖
  mul_hi : ‖q‖ * ‖u * v‖ < 1
  div_lo : ‖q‖ < ‖u * v⁻¹‖
  div_hi : ‖q‖ * ‖u * v⁻¹‖ < 1

end Region

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TateCurve

open scoped NNReal

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u v : K}

section Coefficients

variable (u v)

noncomputable def addDefectSumCoeff (N : ℕ) : K :=
  cauchyMul (xCoeffFull (u * v)) (cauchyMul (xCoeffFull u) (xCoeffFull u)) N
    - 2 * cauchyMul (xCoeffFull (u * v)) (cauchyMul (xCoeffFull u) (xCoeffFull v)) N
    + cauchyMul (xCoeffFull (u * v)) (cauchyMul (xCoeffFull v) (xCoeffFull v)) N
    + cauchyMul (xCoeffFull (u * v⁻¹)) (cauchyMul (xCoeffFull u) (xCoeffFull u)) N
    - 2 * cauchyMul (xCoeffFull (u * v⁻¹)) (cauchyMul (xCoeffFull u) (xCoeffFull v)) N
    + cauchyMul (xCoeffFull (u * v⁻¹)) (cauchyMul (xCoeffFull v) (xCoeffFull v)) N
    - 2 * cauchyMul (xCoeffFull u) (cauchyMul (xCoeffFull u) (xCoeffFull v)) N
    - 2 * cauchyMul (xCoeffFull u) (cauchyMul (xCoeffFull v) (xCoeffFull v)) N
    - cauchyMul (xCoeffFull u) (xCoeffFull v) N
    - 2 * cauchyMul a₄Coeff (xCoeffFull u) N
    - 2 * cauchyMul a₄Coeff (xCoeffFull v) N
    - 4 * a₆Coeff N


end Coefficients

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section TripleSplit

noncomputable def cauchyMulIntTriple (c d e : ℕ → K) (N : ℕ) : K :=
  ∑ i ∈ Finset.Ico 1 N, c i * cauchyMulInt d e (N - i)

end TripleSplit

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TateCurve

open scoped NNReal

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u v : K}

section PsiCoeff

variable (u) in

noncomputable def psiCoeffFull (N : ℕ) : K := 2 * yCoeffFull u N + xCoeffFull u N

end PsiCoeff

section Coefficients

variable (u v) in

noncomputable def addDefectDiffCoeff (N : ℕ) : K :=
  cauchyMul (xCoeffFull (u * v)) (cauchyMul (xCoeffFull u) (xCoeffFull u)) N
    - 2 * cauchyMul (xCoeffFull (u * v)) (cauchyMul (xCoeffFull u) (xCoeffFull v)) N
    + cauchyMul (xCoeffFull (u * v)) (cauchyMul (xCoeffFull v) (xCoeffFull v)) N
    - cauchyMul (xCoeffFull (u * v⁻¹)) (cauchyMul (xCoeffFull u) (xCoeffFull u)) N
    + 2 * cauchyMul (xCoeffFull (u * v⁻¹)) (cauchyMul (xCoeffFull u) (xCoeffFull v)) N
    - cauchyMul (xCoeffFull (u * v⁻¹)) (cauchyMul (xCoeffFull v) (xCoeffFull v)) N
    + cauchyMul (psiCoeffFull u) (psiCoeffFull v) N

end Coefficients

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v w : K}

section Psifun

variable (w) in

noncomputable def psifun : K := 2 * yfun w + xfun w

end Psifun

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section AbsorbedNormalForm

variable (u v) in

noncomputable def svComplex (M : ℕ) : K :=
  2 * ((xfun (u * v) - xfun (u * v⁻¹)) * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M)))
    + (∑ d ∈ M.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * (xfun u - xfun v) ^ 2
    + (∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
        * (2 * ((xfun u - xfun v) * (xCoeff u (M - a) - xCoeff v (M - a)))))
    + (psifun u * psiCoeffFull v M + psiCoeffFull u M * psifun v)

end AbsorbedNormalForm

end TateCurve

open scoped NNReal

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u v w : K}

def LatticeRep (q w w' : K) : Prop :=
  ∃ m : ℤ, w' = q ^ m * w ∨ w' = q ^ m * w⁻¹

def OnHalfLattice (q w : K) : Prop :=
  ∃ m : ℤ, ‖q ^ m * w‖ * ‖q ^ m * w‖ = ‖q‖

end TateCurve

namespace TateCurve

open WeierstrassCurve.Affine

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]

def MuTranslation (q ζ : K) (p : ℕ) : Prop :=
  ∀ a : ℕ, 1 ≤ a → a < p → ∀ u : K, u ≠ 0 → OffLattice q u → OffLattice q (ζ ^ a * u) →
    ∀ (h₁ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ a * u)) (pointY q (ζ ^ a * u)))
      (h₂ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ a)) (pointY q (ζ ^ a)))
      (h₃ : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u)),
      (Point.some (pointX q (ζ ^ a * u)) (pointY q (ζ ^ a * u)) h₁ :
          (curve q).toAffine.Point)
        = Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂
            + Point.some (pointX q u) (pointY q u) h₃

end TateCurve
