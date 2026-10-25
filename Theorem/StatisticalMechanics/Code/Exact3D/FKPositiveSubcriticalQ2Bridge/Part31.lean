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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part32
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem copyDeleteEmbeddingDecrement_fst
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m)
    (a : Sharpness.FluxEdgeCopy.Copy G (Function.update m i.1 (m i.1 - 1))) :
    ((copyDeleteEmbeddingDecrement G m i a).1).1 = a.1 := by
  classical
  rcases i with ⟨e0, r⟩
  rcases a with ⟨e, k⟩
  by_cases he : e = e0
  · subst e
    simp [copyDeleteEmbeddingDecrement]
  · simp [copyDeleteEmbeddingDecrement, he]


theorem copyDeleteEmbeddingDecrement_ends
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m)
    (a : Sharpness.FluxEdgeCopy.Copy G (Function.update m i.1 (m i.1 - 1))) :
    Sharpness.FluxEdgeCopy.endsM G m
        ((copyDeleteEmbeddingDecrement G m i a).1) =
      Sharpness.FluxEdgeCopy.endsM G
        (Function.update m i.1 (m i.1 - 1)) a := by
  simpa [Sharpness.FluxEdgeCopy.endsM]
    using congrArg Subtype.val (copyDeleteEmbeddingDecrement_fst G m i a)


theorem copyDeleteEmbeddingDecrement_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m) :
    Function.Injective
      (fun a :
          Sharpness.FluxEdgeCopy.Copy G
            (Function.update m i.1 (m i.1 - 1)) =>
        (copyDeleteEmbeddingDecrement G m i a).1) := by
  classical
  intro a b hab
  have hedge : a.1 = b.1 := by
    have ha := copyDeleteEmbeddingDecrement_fst G m i a
    have hb := copyDeleteEmbeddingDecrement_fst G m i b
    exact ha.symm.trans ((congrArg Sigma.fst hab).trans hb)
  rcases i with ⟨e0, r⟩
  rcases a with ⟨e, k⟩
  rcases b with ⟨f, l⟩
  simp only at hedge
  subst f
  by_cases he : e = e0
  · subst e
    have hmpos : 0 < m e0 := Nat.lt_of_le_of_lt (Nat.zero_le _) r.2
    have hsize : m e0 - 1 + 1 = m e0 :=
      Nat.sub_one_add_one_eq_of_pos hmpos
    have hupdate :
        Function.update m e0 (m e0 - 1) e0 = m e0 - 1 := by
      simp [Function.update_self]
    let k' : Fin (m e0 - 1) := Fin.cast hupdate k
    let l' : Fin (m e0 - 1) := Fin.cast hupdate l
    let p : Fin ((m e0 - 1) + 1) := Fin.cast hsize.symm r
    have hsub :
        (finSuccAboveEquiv p) k' = (finSuccAboveEquiv p) l' := by
      apply Subtype.ext
      have hidx :
          Fin.cast hsize ((finSuccAboveEquiv p) k').1 =
            Fin.cast hsize ((finSuccAboveEquiv p) l').1 := by
        simpa [copyDeleteEmbeddingDecrement, hupdate, k', l', p] using hab
      apply Fin.ext
      have hv :
          ((Fin.cast hsize
              ((finSuccAboveEquiv p) k').1 : Fin (m e0)) : ℕ) =
            ((Fin.cast hsize
              ((finSuccAboveEquiv p) l').1 : Fin (m e0)) : ℕ) :=
        congrArg (fun z : Fin (m e0) => (z : ℕ)) hidx
      simpa using hv
    have hk' : k' = l' := (finSuccAboveEquiv p).injective hsub
    have hkl : k = l := by
      apply Fin.ext
      have hv : (k' : ℕ) = (l' : ℕ) :=
        congrArg (fun z : Fin (m e0 - 1) => (z : ℕ)) hk'
      simpa [k', l', Fin.cast] using hv
    cases hkl
    rfl
  · have hupdate :
        Function.update m e0 (m e0 - 1) e = m e := by
      simp [Function.update_of_ne he]
    let k' : Fin (m e) := Fin.cast hupdate k
    let l' : Fin (m e) := Fin.cast hupdate l
    have hkl' : k' = l' := by
      simpa [copyDeleteEmbeddingDecrement, he, hupdate, k', l'] using hab
    have hkl : k = l := by
      apply Fin.ext
      have hv : (k' : ℕ) = (l' : ℕ) :=
        congrArg (fun z : Fin (m e) => (z : ℕ)) hkl'
      simpa [k', l', Fin.cast] using hv
    cases hkl
    rfl


end Exact3D
end StatMech
