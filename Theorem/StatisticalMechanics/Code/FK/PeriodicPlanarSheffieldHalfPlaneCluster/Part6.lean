/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneExclusion.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalErgodicity.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisNegation.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster.Part5
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicPlaneEmbedding.shift_image_rightHalfPlaneVertices
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (r : Real) :
    P.shift z '' E.rightHalfPlaneVertices r =
      E.rightHalfPlaneVertices (r + z 0) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    change r + (z 0 : Real) ≤ E.vertexCoord (P.shift z u) 0
    rw [E.vertexCoord_shift]
    simpa [add_comm] using add_le_add_right hu (z 0 : Real)
  · intro hx
    let u := P.shift (-z) x
    have hux : P.shift z u = x := by simp [u]
    refine ⟨u, ?_, hux⟩
    change r ≤ E.vertexCoord u 0
    change r + (z 0 : Real) ≤ E.vertexCoord x 0 at hx
    rw [← hux, E.vertexCoord_shift] at hx
    exact le_of_add_le_add_right hx

theorem PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_translate_preimage
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (r : Real) :
    P.configTranslate z ⁻¹'
        E.rightHalfPlaneHasInfiniteCluster (r + z 0) =
      E.rightHalfPlaneHasInfiniteCluster r := by
  ext omega
  change P.HasInfiniteClusterWithin (P.configTranslate z omega)
      (E.rightHalfPlaneVertices (r + z 0)) ↔
    P.HasInfiniteClusterWithin omega (E.rightHalfPlaneVertices r)
  rw [← E.shift_image_rightHalfPlaneVertices z r]
  exact P.hasInfiniteClusterWithin_configTranslate z omega
    (E.rightHalfPlaneVertices r)

theorem PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measurableSet
    (E : PeriodicPlaneEmbedding P) (r : Real) :
    MeasurableSet (E.rightHalfPlaneHasInfiniteCluster r) :=
  P.measurableSet_hasInfiniteClusterWithin (E.rightHalfPlaneVertices r)

theorem PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_antitone
    (E : PeriodicPlaneEmbedding P) :
    Antitone E.rightHalfPlaneHasInfiniteCluster := by
  intro r s hrs omega homega
  exact P.hasInfiniteClusterWithin_mono omega
    (fun v hv => hrs.trans hv) homega

theorem PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (z : Site 2) (r : Real) :
    mu (E.rightHalfPlaneHasInfiniteCluster (r + z 0)) =
      mu (E.rightHalfPlaneHasInfiniteCluster r) := by
  rw [← E.rightHalfPlaneHasInfiniteCluster_translate_preimage z r]
  exact ((hTI z).measure_preimage
    (E.rightHalfPlaneHasInfiniteCluster_measurableSet
      (r + z 0)).nullMeasurableSet).symm


theorem PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_boundary
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (r s : Real) :
    mu (E.rightHalfPlaneHasInfiniteCluster r) =
      mu (E.rightHalfPlaneHasInfiniteCluster s) := by
  wlog hrs : r ≤ s generalizing r s
  · exact (this s r (le_of_not_ge hrs)).symm
  obtain ⟨n, hn⟩ := exists_nat_ge (s - r)
  let z : Site 2 := fun i => if i = 0 then (n : Int) else 0
  have hz0 : (z 0 : Real) = n := by simp [z]
  have hsn : s ≤ r + (z 0 : Real) := by
    rw [hz0]
    linarith
  have hperiod := E.rightHalfPlaneHasInfiniteCluster_measure_eq mu hTI z r
  apply le_antisymm
  · rw [← hperiod]
    exact measure_mono
      (E.rightHalfPlaneHasInfiniteCluster_antitone hsn)
  · exact measure_mono
      (E.rightHalfPlaneHasInfiniteCluster_antitone hrs)


end StatMech.FK.PeriodicPlanar
