/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetGauge
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismGeometry


namespace StatMech.FrontierA

open StatMech Lattice Sharpness


def rectangularPrismSiteCentered (n : Nat)
    (v : StatMech.Ising.RectangularPrismSite
      (2 * n + 1) (2 * n + 1) n) : Site 3 :=
  fun i => if i = (0 : Fin 3) then (finOddEquivCenteredInt n v.x).1
    else if i = (1 : Fin 3) then (finOddEquivCenteredInt n v.y).1
    else (finOddEquivCenteredInt n v.z).1

def rectangularPrismSiteEquivSctBox (n : Nat) :
    StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n ≃
      {x : Site 3 // x ∈ box 3 n} where
  toFun v := ⟨rectangularPrismSiteCentered n v, by
    intro i
    fin_cases i
    · exact (finOddEquivCenteredInt n v.x).2
    · exact (finOddEquivCenteredInt n v.y).2
    · exact (finOddEquivCenteredInt n v.z).2⟩
  invFun z :=
    ⟨(finOddEquivCenteredInt n).symm ⟨z.1 0, z.2 0⟩,
      (finOddEquivCenteredInt n).symm ⟨z.1 1, z.2 1⟩,
      (finOddEquivCenteredInt n).symm ⟨z.1 2, z.2 2⟩⟩
  left_inv v := by
    rcases v with ⟨x, y, z⟩
    rw [StatMech.Ising.RectangularPrismSite.mk.injEq]
    simp only [rectangularPrismSiteCentered, if_pos, Fin.isValue]
    exact ⟨(finOddEquivCenteredInt n).symm_apply_apply x,
      (finOddEquivCenteredInt n).symm_apply_apply y,
      (finOddEquivCenteredInt n).symm_apply_apply z⟩
  right_inv z := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [rectangularPrismSiteCentered]


def reflectThirdBoxEquiv (n : Nat) :
    {x : Site 3 // x ∈ box 3 n} ≃ {x : Site 3 // x ∈ box 3 n} where
  toFun x := ⟨fun i => if i = (2 : Fin 3) then -x.1 i else x.1 i, by
    intro i
    by_cases hi : i = (2 : Fin 3)
    · subst i
      simpa using x.2 (2 : Fin 3)
    · simpa [hi] using x.2 i
  ⟩
  invFun x := ⟨fun i => if i = (2 : Fin 3) then -x.1 i else x.1 i, by
    intro i
    by_cases hi : i = (2 : Fin 3)
    · subst i
      simpa using x.2 (2 : Fin 3)
    · simpa [hi] using x.2 i
  ⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i = (2 : Fin 3) <;> simp [hi]
  right_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i = (2 : Fin 3) <;> simp [hi]


def rectangularPrismSiteEquivSctBoxDobrushin (n : Nat) :
    StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n ≃
      {x : Site 3 // x ∈ box 3 n} :=
  (rectangularPrismSiteEquivSctBox n).trans (reflectThirdBoxEquiv n)

end StatMech.FrontierA
