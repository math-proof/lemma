/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardExtraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.DyadicInverseSquareSummability.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.HadamardQuadraticFactorOrder
import Theorem.StatisticalMechanics.Code.FrontierA.EntireOrderMatchedQuotient
import Theorem.StatisticalMechanics.Code.FrontierA.EntireZeroFreeLogarithm
import Theorem.StatisticalMechanics.Code.FrontierA.EntireExponentialLogAffine
import Theorem.StatisticalMechanics.Code.FrontierA.EntireExponentialCharacteristicAffine
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Lindelof
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardExtraction.Part6
open Filter Metric
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

noncomputable section

theorem positiveImaginaryZeroCopiesBelowToDisk_injective
    {F : Complex → Complex} {R : Real} (hR : 0 ≤ R) :
    Function.Injective (positiveImaginaryZeroCopiesBelowToDisk
      (F := F) (R := R) hR) := by
  intro q r h
  apply Subtype.ext
  cases q with
  | mk q hq =>
      cases r with
      | mk r hr =>
          dsimp only [positiveImaginaryZeroCopiesBelowToDisk] at h ⊢
          have hloc := congrArg
            (fun p : entireDiskZeroCopies F R => p.1.1.im) h
          have hy : q.1 = r.1 := by
            apply Subtype.ext
            simpa using hloc
          cases q with
          | mk y i =>
              cases r with
              | mk y' j =>
                  dsimp at hy ⊢
                  subst y'
                  have hi := congrArg
                    (fun p : entireDiskZeroCopies F R => p.2.1) h
                  exact Sigma.ext rfl (by
                    exact heq_of_eq (Fin.ext hi))

theorem EvenExponentialTypeImaginaryZeros.card_positiveImaginaryZeroCopiesBelow_le_divisor
    {F : Complex → Complex} (hF : EvenExponentialTypeImaginaryZeros F)
    {R : Real} (hR : 0 ≤ R) :
    (Nat.card (positiveImaginaryZeroCopiesBelow F R) : Int) ≤
      ∑ᶠ z : Complex, (MeromorphicOn.divisor F (closedBall 0 R)) z := by
  letI : Finite (positiveImaginaryZeroCopiesBelow F R) :=
    hF.positiveImaginaryZeroCopiesBelow_finite R |>.to_subtype
  letI := hF.entireDiskZeroCopies_finite R
  have hcard := Nat.card_le_card_of_injective
    (positiveImaginaryZeroCopiesBelowToDisk (F := F) (R := R) hR)
    (positiveImaginaryZeroCopiesBelowToDisk_injective
      (F := F) (R := R) hR)
  have hcardInt :
      (Nat.card (positiveImaginaryZeroCopiesBelow F R) : Int) ≤
        (Nat.card (entireDiskZeroCopies F R) : Int) := by
    exact_mod_cast hcard
  rw [hF.card_entireDiskZeroCopies_eq_finsum_divisor R] at hcardInt
  exact hcardInt


end
end StatMech.FrontierA
