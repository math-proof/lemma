/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part36
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectBoundaryFiniteLayerSum_eq_listCoefficientSum
    {W : Nat} (hW : 0 < W) (q : Real)
    (state : FKRectBoundaryState W) (n : Nat) (parity : Fin n -> Bool) :
    (∑ layers : Fin n -> Bool × Fin W -> Bool,
      fkRectBoundaryRunWeight hW q state
          (List.ofFn fun i : Fin n => (parity i, layers i)) *
        fkRectBoundarySeamFunctional hW q
          (fkRectBoundaryRunState hW state
            (List.ofFn fun i : Fin n => (parity i, layers i)))) =
      fkRectBoundaryListCoefficientSum hW q state
        (List.ofFn parity) := by
  induction n generalizing state with
  | zero =>
      simp [fkRectBoundaryRunWeight, fkRectBoundaryRunState,
        fkRectBoundaryListCoefficientSum]
  | succ n ih =>
      let A := Bool × Fin W -> Bool
      let split : (Fin (n + 1) -> A) ≃ A × (Fin n -> A) :=
        finFunctionConsEquiv n A
      calc
        (∑ layers : Fin (n + 1) -> A,
          fkRectBoundaryRunWeight hW q state
              (List.ofFn fun i : Fin (n + 1) =>
                (parity i, layers i)) *
            fkRectBoundarySeamFunctional hW q
              (fkRectBoundaryRunState hW state
                (List.ofFn fun i : Fin (n + 1) =>
                  (parity i, layers i)))) =
            ∑ p : A × (Fin n -> A),
              fkRectBoundaryRunWeight hW q state
                  ((parity 0, p.1) :: List.ofFn fun i : Fin n =>
                    (parity i.succ, p.2 i)) *
                fkRectBoundarySeamFunctional hW q
                  (fkRectBoundaryRunState hW state
                    ((parity 0, p.1) :: List.ofFn fun i : Fin n =>
                      (parity i.succ, p.2 i))) := by
                apply Fintype.sum_equiv split
                intro layers
                simp [split, A, List.ofFn_succ]
        _ = ∑ eta : A, ∑ layers : Fin n -> A,
              fkRectBoundaryLayerWeight hW q (parity 0) state eta *
                (fkRectBoundaryRunWeight hW q
                    (fkRectBoundaryLayerOutput hW (parity 0) state eta)
                    (List.ofFn fun i : Fin n =>
                      (parity i.succ, layers i)) *
                  fkRectBoundarySeamFunctional hW q
                    (fkRectBoundaryRunState hW
                      (fkRectBoundaryLayerOutput hW (parity 0) state eta)
                      (List.ofFn fun i : Fin n =>
                        (parity i.succ, layers i)))) := by
                rw [Fintype.sum_prod_type]
                simp only [fkRectBoundaryRunWeight,
                  fkRectBoundaryRunState]
                ring
        _ = ∑ eta : A,
              fkRectBoundaryLayerWeight hW q (parity 0) state eta *
                fkRectBoundaryListCoefficientSum hW q
                  (fkRectBoundaryLayerOutput hW (parity 0) state eta)
                  (List.ofFn fun i : Fin n => parity i.succ) := by
                apply Finset.sum_congr rfl
                intro eta heta
                rw [← ih, Finset.mul_sum]
        _ = fkRectBoundaryListCoefficientSum hW q state
              (List.ofFn parity) := by
                rw [List.ofFn_succ]
                rfl


end
end StatMech.FrontierD
