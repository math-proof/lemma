/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc44flow.Part2
import Def.StatisticalMechanics.Code.Walls.gc45cycle.Part3
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc45_FibreDomReloc_of_nullityOneReloc (ends : ι → Sym2 W) (o x y g : W)
    (htree : gc45_TreeLHS ends o x y g)
    (hreloc : gc45_NullityOneRelocation ends o x y g) :
    gc43_FibreDomReloc ends o x y g := by
  obtain ⟨φ, hmaps, hcount⟩ := hreloc
  exact gc45_fibreDomReloc_of_count_le ends o x y g htree φ hmaps hcount


theorem gc45_EMassResidue_of_nullityOneReloc (ends : ι → Sym2 W) (o x y g : W)
    (htree : gc45_TreeLHS ends o x y g)
    (hreloc : gc45_NullityOneRelocation ends o x y g) :
    gc42_EMassResidue ends o x y g :=
  gc43_EMass_of_fibreDomReloc ends o x y g
    (gc45_FibreDomReloc_of_nullityOneReloc ends o x y g htree hreloc)


theorem gc45_countIneq_of_nullityOneReloc (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (htree : gc45_TreeLHS ends o x y g)
    (hreloc : gc45_NullityOneRelocation ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc43_countIneq_of_fibreDomReloc ends hnd hox hoy hog hxy hxg hyg huniv
    (gc45_FibreDomReloc_of_nullityOneReloc ends o x y g htree hreloc)

end Abstract
end StatMech.Walls
