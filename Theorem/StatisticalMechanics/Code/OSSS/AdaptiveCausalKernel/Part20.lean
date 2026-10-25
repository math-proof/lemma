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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part20
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


theorem tripleCube_measurePreserving (n : ℕ) :
    MeasurePreserving
      (fun z : Fin n → ((ℝ × ℝ) × ℝ) =>
        ((fun i => (z i).1.1, fun i => (z i).1.2), fun i => (z i).2))
      (tripleCube n)
      (((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)).prod
        (GrandCoupling.Vcube n)) := by
  let ν := volume.restrict (Set.Icc (0 : ℝ) 1)
  have houter := measurePreserving_arrowProdEquivProdArrow (ℝ × ℝ) ℝ (Fin n)
    (fun _ => ν.prod ν) (fun _ => ν)
  have hinner := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ => ν) (fun _ => ν)
  have hid : MeasurePreserving (id : (Fin n → ℝ) → (Fin n → ℝ))
      (GrandCoupling.Vcube n) (GrandCoupling.Vcube n) :=
    MeasurePreserving.id (GrandCoupling.Vcube n)
  have hprod := hinner.prod hid
  simpa [tripleCube, GrandCoupling.Vcube, ν, Function.comp_def] using hprod.comp houter

theorem tripleCubeEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (tripleCubeEquiv n) (tripleCube n)
      (((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)).prod
        (GrandCoupling.Vcube n)) := by
  simpa [tripleCubeEquiv, MeasurableEquiv.trans_apply, Function.comp_def] using
    tripleCube_measurePreserving n

theorem tripleCube_integral_equiv (n : ℕ)
    (g : (((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ)) → ℝ) :
    (∫ z, g (tripleCubeEquiv n z) ∂(tripleCube n)) =
      ∫ p, g p ∂(((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)).prod
        (GrandCoupling.Vcube n)) := by
  exact (tripleCubeEquiv_measurePreserving n).integral_comp
    (tripleCubeEquiv n).measurableEmbedding g

theorem tripleCube_frozenCrossCodeAtom (μ : ConfigSpace E → ℝ)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    tripleCube (Fintype.card E) (frozenCrossCodeAtom μ S base left right) =
      ∏ i : Fin (Fintype.card E),
        let ν := volume.restrict (Set.Icc (0 : ℝ) 1)
        (ν.prod ν).prod ν (crossRawTriple μ S base left right i) := by
  rw [frozenCrossCodeAtom_eq_rawTripleBox, tripleCube, Measure.pi_pi]

end AdaptiveCausalKernel
end OSSS
end StatMech
