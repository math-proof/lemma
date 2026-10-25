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
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part30
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

noncomputable def copyDeleteEmbeddingDecrement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m) :
    Sharpness.FluxEdgeCopy.Copy G (Function.update m i.1 (m i.1 - 1)) →
      {j : Sharpness.FluxEdgeCopy.Copy G m // j ≠ i} := by
  classical
  intro a
  rcases i with ⟨e0, r⟩
  rcases a with ⟨e, k⟩
  by_cases he : e = e0
  · subst e
    have hmpos : 0 < m e0 := Nat.lt_of_le_of_lt (Nat.zero_le _) r.2
    have hsize : m e0 - 1 + 1 = m e0 :=
      Nat.sub_one_add_one_eq_of_pos hmpos
    have hupdate :
        Function.update m e0 (m e0 - 1) e0 = m e0 - 1 := by
      simp [Function.update_self]
    let k' : Fin (m e0 - 1) := Fin.cast hupdate k
    let p : Fin ((m e0 - 1) + 1) := Fin.cast hsize.symm r
    let xSubtype : {x : Fin ((m e0 - 1) + 1) // x ≠ p} :=
      finSuccAboveEquiv p k'
    refine ⟨⟨e0, Fin.cast hsize xSubtype.1⟩, ?_⟩
    intro hji
    have hidx_heq : HEq (Fin.cast hsize xSubtype.1) r :=
      (Sigma.mk.inj_iff.mp hji).2
    have hidx : Fin.cast hsize xSubtype.1 = r := eq_of_heq hidx_heq
    apply xSubtype.2
    apply Fin.ext
    have hv := congrArg Fin.val hidx
    simpa [p] using hv
  · have hupdate :
        Function.update m e0 (m e0 - 1) e = m e := by
      simp [Function.update_of_ne he]
    let k' : Fin (m e) := Fin.cast hupdate k
    refine ⟨⟨e, k'⟩, ?_⟩
    intro hji
    apply he
    exact congrArg Sigma.fst hji


end Exact3D
end StatMech
