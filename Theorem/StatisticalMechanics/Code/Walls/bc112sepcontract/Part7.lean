/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc110globalforest
import Theorem.StatisticalMechanics.Code.Walls.bc106separated.Part3
import Def.StatisticalMechanics.Code.Walls.bc112sepcontract.Part7
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc112_boundaryLeafResidue_iff_full (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    bc112_BoundaryLeafResidue ω L R ↔ bc106_SeparatedContractedTrifGraph ω L R := by
  constructor
  · rintro ⟨S, hSfin, hSne, G, hGdec, hFdec, ιU, hnbr, hιinj, hmin, hleaf⟩
    exact ⟨S, hSfin, hSne, G, hGdec, hFdec, ιU, hnbr, hmin, hιinj, hleaf⟩
  · rintro ⟨S, hSfin, hSne, G, hGdec, hFdec, ιU, hnbr, hmin, hιinj, hleaf⟩
    exact ⟨S, hSfin, hSne, G, hGdec, hFdec, ιU, hnbr, hιinj, hmin, hleaf⟩


theorem bc112_status :
    
    (∀ (hd : 1 ≤ d) (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 3 ≤ L →
      bc112_SeparatedArmGraph ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc112_BoundaryLeafResidue ω L R ↔ bc106_SeparatedContractedTrifGraph ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc103_ContractedTrifGraph ω L R → bc112_SeparatedArmGraph ω L R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hd ω L R hL; exact bc112_separatedArmGraph_holds hd ω L R hL
  · intro ω L R; exact bc112_boundaryLeafResidue_iff_full ω L R
  · intro ω L R h; exact bc112_separatedArmGraph_of_bc103 ω L R h

end StatMech.Walls
