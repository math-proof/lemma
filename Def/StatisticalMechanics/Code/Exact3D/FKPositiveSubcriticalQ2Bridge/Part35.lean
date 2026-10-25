/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part33
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

noncomputable def copyDeletePreimageDecrement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m) :
    {j : Sharpness.FluxEdgeCopy.Copy G m // j ≠ i} →
      Sharpness.FluxEdgeCopy.Copy G
        (Function.update m i.1 (m i.1 - 1)) := by
  classical
  intro j
  rcases i with ⟨e0, r⟩
  rcases j with ⟨⟨e, k⟩, hjne⟩
  by_cases he : e = e0
  · subst e
    have hmpos : 0 < m e0 := Nat.lt_of_le_of_lt (Nat.zero_le _) r.2
    have hsize : m e0 - 1 + 1 = m e0 :=
      Nat.sub_one_add_one_eq_of_pos hmpos
    let p : Fin ((m e0 - 1) + 1) := Fin.cast hsize.symm r
    let x : Fin ((m e0 - 1) + 1) := Fin.cast hsize.symm k
    have hxne : x ≠ p := by
      intro hxp
      apply hjne
      have hkr : k = r := by
        apply Fin.ext
        have hv : (x : ℕ) = (p : ℕ) :=
          congrArg (fun z : Fin ((m e0 - 1) + 1) => (z : ℕ)) hxp
        simpa [x, p] using hv
      cases hkr
      rfl
    let kDec : Fin (m e0 - 1) :=
      (finSuccAboveEquiv p).symm ⟨x, hxne⟩
    have hupdate :
        Function.update m e0 (m e0 - 1) e0 = m e0 - 1 := by
      simp [Function.update_self]
    exact ⟨e0, Fin.cast hupdate.symm kDec⟩
  · have hupdate :
        Function.update m e0 (m e0 - 1) e = m e := by
      simp [Function.update_of_ne he]
    exact ⟨e, Fin.cast hupdate.symm k⟩


end Exact3D
end StatMech
