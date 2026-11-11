/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CramerTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Probability.code.CramerRateIDCore
open InformationTheory MeasureTheory ProbabilityMeasure ProbabilityTheory Filter
open scoped InnerProductSpace ENNReal Topology

/-!
# Cramér rate-ID re-export

Thin module re-exporting `CramerRateIDCore` for the Probability atlas import.

The public `(hMGF)(hbdd)` Cramér entry
`SatisfiesLDP empiricalMeanLawPi cramerRateFunction` lives in
`Lemma.Random.SatisfiesLDP_EmpiricalMeanLawPi.of.HasFiniteMGF.ForallBddAbove`
(Sanov half in
`Lemma.Random.SatisfiesLDP_EmpiricalMeanLawPi_CramerRateFromSanov.of.All_BddAbove.HasFiniteMGF`).
Theorem-side residual wrappers that still take an explicit Sanov-mean `hLDP` remain in
`CramerRateIDCore` / `CramerBarycenter`
(`cramer_theorem_of_HasFiniteMGF_of_forall_bddAbove_of_meanSanovLDP`,
`…_of_HasEmpiricalMeanSanovLDP`).
-/
