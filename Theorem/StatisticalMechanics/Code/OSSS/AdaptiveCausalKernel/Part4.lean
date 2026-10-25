/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw.Part3
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
import Theorem.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part4
import Theorem.StatisticalMechanics.Code.OSSS.PredictableTreeQuery
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part4
open scoped BigOperators
open MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace OSSS

namespace AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem pairedCube_measurePreserving (n : ℕ) :
    MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
      (pairedCube n) ((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)) := by
  simpa [pairedCube, GrandCoupling.Vcube] using
    (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
      (fun _ => volume.restrict (Set.Icc (0 : ℝ) 1))
      (fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)))

theorem pairedCube_integral_equiv (n : ℕ)
    (g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) :
    (∫ z, g (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n) z)
        ∂(pairedCube n)) =
      ∫ p, g p ∂((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)) := by
  exact (pairedCube_measurePreserving n).integral_comp
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)).measurableEmbedding g


theorem pairedCube_frozenCodeAtom (mu : ConfigSpace E → ℝ)
    (S : CausalOrder (Finset.univ : Finset E))
    (base target : ConfigSpace E) :
    pairedCube (Fintype.card E) (frozenCodeAtom mu S base target) =
      ∏ i : Fin (Fintype.card E),
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
          (volume.restrict (Set.Icc (0 : ℝ) 1)))
            (frozenRawPair mu S base target i) := by
  rw [frozenCodeAtom_eq_rawPairBox, pairedCube, Measure.pi_pi]

end AdaptiveCausalKernel
end OSSS
end StatMech
