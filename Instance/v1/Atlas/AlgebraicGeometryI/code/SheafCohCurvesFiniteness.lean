/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohCurvesFiniteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohomology
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CoherentSheavesCurves
import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness.Part2


namespace SheafCohCurvesFiniteness

open CohomologyP1 SheafCohomology


section TwoTermComplex

variable (k : Type*) [Field k]

attribute [instance] CechComplex2.inst0 CechComplex2.inst1
  CechComplex2.mod0 CechComplex2.mod1

/-- Finiteness of `H⁰(O_{ℙ¹}(n))`: it is `k`-supported on the finite set `[0, n]`. -/
noncomputable instance cechH0_finiteDim_P1 (n : ℤ) :
    Module.Finite k ↥(CechH0 k n) := by
  rw [cechH0_eq_supported]
  exact finiteDim_supported k (Set.Icc 0 n)

/-- Finiteness of `H¹(O_{ℙ¹}(n))`: it is realized by Laurent terms with indices
strictly between `n` and `0`, a finite range. -/
noncomputable instance cechH1_finiteDim_P1 (n : ℤ) :
    Module.Finite k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) := by
  haveI : Module.Finite k ↥(Finsupp.supported k k (Set.Ioo n (0 : ℤ))) :=
    finiteDim_supported k (Set.Ioo n 0)
  exact Module.Finite.equiv (H1_equiv_supported_complement k n).symm

end TwoTermComplex
end SheafCohCurvesFiniteness
