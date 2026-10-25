/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessDensity
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose2
import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part3
import Theorem.StatisticalMechanics.Code.FK.HolleyCoupling.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPointInfinite.Part5
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.Foundations.Strassen
import Def.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part2
open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {E : Type*} [Fintype E] [DecidableEq E]


variable {d : ℕ}


theorem fuc_fk_uniqueness (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hdata : fuc_HomogeneousFreeEnergyData d N) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  obtain ⟨g, hg, hwired, hfree⟩ := hdata
  
  choose P hP using fuc_hcoup d N
  
  exact fud_countable_phi_ne_of_homogeneous
    (fun t => fuc_freeMass d N t) (fun t => fuc_wiredMass d N t) eb P hP
    (a := pressureLeftDeriv g) (b := pressureRightDeriv g) (g := g)
    
    (fuc_hmono d N eb)
    
    hg
    
    (fun e' t => by rw [fuc_edgeMargProb_free]; exact hfree e' t)
    
    (fun e' t => by rw [fuc_edgeMargProb_wired]; exact hwired e' t)
    
    (fun _ => rfl)
    
    (fun _ => rfl)


theorem fuc_homogeneousData_imp_fsc (d N : ℕ) (eb : Sym2 (boxVerts d N))
    (hdata : fuc_HomogeneousFreeEnergyData d N) :
    fsc_FreeEnergyData d N eb := by
  obtain ⟨g, hg, hwired, hfree⟩ := hdata
  exact ⟨g, hg, fun t => hwired eb t, fun t => hfree eb t⟩

end FK
end StatMech
