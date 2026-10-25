/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TwistSheaf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.QCohProjective.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.QCohProjective
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.QCohEquivalenceProof
import Instance.v1.Atlas.AlgebraicGeometryI.code.QCohEquivalenceProof
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.TwistSheaf
set_option maxHeartbeats 4000000

open MvPolynomial QCohProjective


noncomputable section

namespace TwistSheaf

variable (k : Type*) [Field k] (n : ℕ)


/-- Graded multiplication: multiplying a degree-`i` homogeneous polynomial
with a degree-`j` graded element gives a degree-`(i+j)` graded element. -/
def polyGsmul (i : ℕ) (j : ℤ) :
    gradedComponent k n i → polyGrComp k n j → polyGrComp k n (↑i + j) :=
  fun ⟨s, hs⟩ ⟨m, hm⟩ => by
    refine ⟨s * m, ?_⟩
    by_cases hj : 0 ≤ j
    ·
      simp only [polyGrSub, if_pos hj] at hm
      simp only [polyGrSub, if_pos (by omega : (0 : ℤ) ≤ ↑i + j)]
      show (s * m).IsHomogeneous (↑i + j).toNat
      have hs' : s.IsHomogeneous i := hs
      have hm' : m.IsHomogeneous j.toNat := hm
      convert hs'.mul hm' using 1
      omega
    ·
      push Not at hj
      simp only [polyGrSub, if_neg (by omega : ¬(0 ≤ j))] at hm
      replace hm : m = 0 := by simpa using hm
      rw [hm, mul_zero]
      exact Submodule.zero_mem _

/-- Graded-module data realizing the structure sheaf of `P^n` as the trivial
shift: the graded pieces are the homogeneous components of `k[X₀,…,Xₙ]`. -/
def structureSheafData : GradedModuleData k n where
  component := polyGrComp k n
  instACG := fun _ => inferInstance
  instMod := fun _ => inferInstance
  gsmul := polyGsmul k n

/-- The Serre twist `O(d)` on `P^n`, expressed as the graded-module data
obtained by shifting the structure sheaf by `d`. -/
def serreTwist (d : ℤ) : GradedModuleData k n :=
  (structureSheafData k n).twist d

end TwistSheaf
end
