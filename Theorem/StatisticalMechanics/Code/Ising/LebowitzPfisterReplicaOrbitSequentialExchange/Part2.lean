/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 800000 in


theorem lpReplicaCoupledReflectToggle_currentSources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    let target := lpReplicaCollisionProfile G sites
      (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
      (profileFlux (lpReplicaCurrentGraph G sites) m P)
    let T := lpReplicaCurrentCopies G sites m tag row current
    let U := lpReplicaCurrentCopies G sites m tag (!row) current
    StatMech.Sharpness.RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites) target)
        (lpReplicaCurrentCopies G sites target
          (lpReplicaCoupledReflectToggleTagRaw G sites m P tag)
          row current) =
      (StatMech.Sharpness.RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites) m) T ∆
        StatMech.Sharpness.RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites) m) (T ∩ P)) ∆
        (StatMech.Sharpness.RandomCurrent.sources
          (endsM (lpReplicaCurrentGraph G sites) m) (U ∩ P)).map
            lpReplicaCurrentReflect.toEmbedding := by
  classical
  dsimp only
  unfold lpReplicaCoupledReflectToggleTagRaw
  let T := lpReplicaCurrentCopies G sites m tag row current
  let U := lpReplicaCurrentCopies G sites m tag (!row) current
  let Q := P.filter fun c => (tag c).2 = current
  have houtside : (T ∆ Q) \ P = T \ P := by
    ext c
    rcases htag : tag c with ⟨r, q⟩
    cases r <;> cases q <;> cases row <;> cases current <;>
      simp [T, Q, lpReplicaCurrentCopies, htag, Finset.mem_symmDiff]
  have hinside : (T ∆ Q) ∩ P = U ∩ P := by
    ext c
    rcases htag : tag c with ⟨r, q⟩
    cases r <;> cases q <;> cases row <;> cases current <;>
      simp [T, U, Q, lpReplicaCurrentCopies, htag, Finset.mem_symmDiff]
  have hinter : T ∩ P ⊆ T := Finset.inter_subset_left
  have hdiff : T \ P = T \ (T ∩ P) := by
    ext c
    simp
  rw [lpReplicaCurrentCopies_partialReflectTagRaw,
    lpReplicaCurrentCopies_toggle,
    lpReplicaPartialReflectCopiesRaw_sources,
    houtside, hinside, hdiff,
    sources_sdiff_of_subset hinter]


theorem lpReplicaCurrentReflect_map_involutive
    (X : Finset (LPReplicaCurrentVertex V)) :
    (X.map lpReplicaCurrentReflect.toEmbedding).map
        lpReplicaCurrentReflect.toEmbedding = X := by
  ext x
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, hzy⟩, hyx⟩
    change lpReplicaCurrentReflect z = y at hzy
    change lpReplicaCurrentReflect y = x at hyx
    subst y
    rw [lpReplicaCurrentReflect_involutive] at hyx
    simpa [← hyx] using hz
  · intro hx
    refine ⟨lpReplicaCurrentReflect x, ?_,
      lpReplicaCurrentReflect_involutive x⟩
    exact ⟨x, hx, rfl⟩


theorem lpReplicaRowGate_coupledReflectToggle
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (A B X0 X1 Z0 Z1 : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (hfalse0 : StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentCopies G sites m tag false false ∩ P) = X0)
    (hfalse1 : StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentCopies G sites m tag true false ∩ P) = X1)
    (htrue0 : StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentCopies G sites m tag false true ∩ P) = Z0)
    (htrue1 : StatMech.Sharpness.RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentCopies G sites m tag true true ∩ P) = Z1)
    (htruePair : Z0 = Z1.map lpReplicaCurrentReflect.toEmbedding)
    (hdisc0 : ¬ StatMech.Sharpness.RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P)))
      (lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaCoupledReflectToggleTagRaw G sites m P tag) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
    (hdisc1 : ¬ StatMech.Sharpness.RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P)))
      (lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaCoupledReflectToggleTagRaw G sites m P tag) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P))
      ((A ∆ X0) ∆ X1.map lpReplicaCurrentReflect.toEmbedding)
      ((B ∆ X1) ∆ X0.map lpReplicaCurrentReflect.toEmbedding)
      (lpReplicaCoupledReflectToggleTagRaw G sites m P tag) := by
  unfold LPReplicaRowGate
  refine ⟨?_, ?_, hdisc0, ?_, ?_, hdisc1⟩
  · rw [lpReplicaCoupledReflectToggle_currentSources,
      hgate.1, hfalse0]
    simp only [Bool.not_false, hfalse1]
  · rw [lpReplicaCoupledReflectToggle_currentSources,
      hgate.2.1, htrue0]
    simp only [Bool.not_false, htrue1]
    rw [htruePair]
    simp
  · rw [lpReplicaCoupledReflectToggle_currentSources,
      hgate.2.2.2.1, hfalse1]
    simp only [Bool.not_true, hfalse0]
  · rw [lpReplicaCoupledReflectToggle_currentSources,
      hgate.2.2.2.2.1, htrue1]
    simp only [Bool.not_true, htrue0]
    rw [htruePair, lpReplicaCurrentReflect_map_involutive]
    simp


end
end StatMech.Ising
