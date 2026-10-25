/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKPressureDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part3
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.FeketeLimit
import Theorem.StatisticalMechanics.Code.FK.ConvexDerivLimit
import Theorem.StatisticalMechanics.Code.FK.IVPressureConvex.Part5
import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBeta.Part4
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Def.StatisticalMechanics.Code.FK.FKPressureDeriv.Part3
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {d : ℕ}


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fpd_homogeneousFreeEnergyData_of_densityDeriv (d N : ℕ) {g : ℝ → ℝ}
    (hg : ConvexOn ℝ univ g) (hres : fpd_IVDensityIsOneSidedDeriv d N g) :
    fuc_HomogeneousFreeEnergyData d N :=
  ⟨g, hg, hres.1, hres.2⟩


theorem fpd_fk_uniqueness (d N : ℕ) (eb : Sym2 (boxVerts d N)) {g : ℝ → ℝ}
    (hg : ConvexOn ℝ univ g) (hres : fpd_IVDensityIsOneSidedDeriv d N g) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  fuc_fk_uniqueness d N eb (fpd_homogeneousFreeEnergyData_of_densityDeriv d N hg hres)


theorem fpd_densityDeriv_imp_fsc (d N : ℕ) {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hres : fpd_IVDensityIsOneSidedDeriv d N g) (e' : Sym2 (boxVerts d N)) :
    fsc_FreeEnergyData d N e' :=
  ⟨g, hg, fun t => hres.1 e' t, fun t => hres.2 e' t⟩


theorem fpd_homogeneousFreeEnergyData_iff (d N : ℕ) :
    fuc_HomogeneousFreeEnergyData d N
      ↔ ∃ g : ℝ → ℝ, ConvexOn ℝ univ g ∧ fpd_IVDensityIsOneSidedDeriv d N g := by
  constructor
  · rintro ⟨g, hg, hw, hf⟩; exact ⟨g, hg, hw, hf⟩
  · rintro ⟨g, hg, hres⟩
    exact fpd_homogeneousFreeEnergyData_of_densityDeriv d N hg hres

end FK
end StatMech
