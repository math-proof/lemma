/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic
import Def.NumberTheory.RothAuxiliary.Part2
set_option maxHeartbeats 999999

open scoped BigOperators

/-!
This file contains the auxiliary-polynomial machinery shared by Roth's theorem and Ridout's
S-adic extension. The public theorem abstracts their integrality difference as finite divisibility
data; the ordinary archimedean theorem is the specialization with no divisibility places.
-/


namespace MathlibExt.NumberTheory.RothAuxiliary

open scoped BigOperators nonZeroDivisors Polynomial

attribute [local instance] Matrix.seminormedAddCommGroup

structure RothIntegralFactorData {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) ℤ} {r : Fin (n + 1) → ℕ}
    (d : RothDeterminantData P r) where
  coeffIndex : RothMvIndex n
  coeff_ne : d.V.coeff coeffIndex ≠ 0
  WZ : ℤ[X]
  WZ_ne : WZ ≠ 0
  WZ_degree : WZ.natDegree ≤ d.k * r (Fin.last n)
  WZ_l1 : rothPolyL1 WZ ≤
    (d.k * r (Fin.last n) + 1) *
      (d.k.factorial * (2 ^ (∑ h, r h) * rothMvL1 P) ^ d.k)
  scaled_factorization :
    rothLastEquiv ℚ n
        ((d.V.coeff coeffIndex : ℚ) •
          MvPolynomial.map (algebraMap ℤ ℚ) d.U) =
      Polynomial.C (MvPolynomial.map (algebraMap ℤ ℚ) d.V) *
        Polynomial.map MvPolynomial.C
          (Polynomial.map (algebraMap ℤ ℚ) WZ)

end MathlibExt.NumberTheory.RothAuxiliary
