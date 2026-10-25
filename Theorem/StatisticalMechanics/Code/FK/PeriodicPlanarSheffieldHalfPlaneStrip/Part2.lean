/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneTranslation.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneStrip
open Filter MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicPlaneEmbedding.rightHalfPlaneStripVertices_subset
    (E : PeriodicPlaneEmbedding P) (r : Real) (n : Nat) :
    E.rightHalfPlaneStripVertices r n ⊆ E.rightHalfPlaneVertices r :=
  fun _ hx => hx.1

theorem PeriodicPlaneEmbedding.rightHalfPlaneStripVertices_mono
    (E : PeriodicPlaneEmbedding P) (r : Real) :
    Monotone (E.rightHalfPlaneStripVertices r) := by
  intro n N hnN x hx
  change x ∈ E.rightHalfPlaneVertices r ∧
    E.vertexCoord x 0 ≤ r + (n : Real) at hx
  change x ∈ E.rightHalfPlaneVertices r ∧
    E.vertexCoord x 0 ≤ r + (N : Real)
  refine ⟨hx.1, ?_⟩
  have hcast : (n : Real) ≤ N := by exact_mod_cast hnN
  linarith


theorem PeriodicPlaneEmbedding.connectedWithin_rightHalfPlane_exists_strip
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V))
    (r : Real) (x y : V)
    (hxy : omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x y) :
    ∃ n : Nat,
      omega ∈ P.connectedWithinSet (E.rightHalfPlaneStripVertices r n) x y := by
  rcases hxy with ⟨l, hchain, hlast, hregion⟩
  let M : Real := ∑ v ∈ (x :: l).toFinset, |E.vertexCoord v 0 - r|
  obtain ⟨n, hn⟩ := exists_nat_ge M
  refine ⟨n, l, hchain, hlast, ?_⟩
  intro v hv
  have hvH := hregion v hv
  refine ⟨hvH, ?_⟩
  have hvfin : v ∈ (x :: l).toFinset := by simpa using hv
  have hterm : |E.vertexCoord v 0 - r| ≤ M := by
    dsimp only [M]
    exact Finset.single_le_sum
      (fun w _hw => abs_nonneg (E.vertexCoord w 0 - r)) hvfin
  have hdiff : E.vertexCoord v 0 - r ≤ M :=
    (le_abs_self (E.vertexCoord v 0 - r)).trans hterm
  change E.vertexCoord v 0 ≤ r + (n : Real)
  linarith

theorem PeriodicPlaneEmbedding.iUnion_connectedWithin_rightHalfPlaneStrip
    (E : PeriodicPlaneEmbedding P) (r : Real) (x y : V) :
    (⋃ n : Nat, P.connectedWithinSet
        (E.rightHalfPlaneStripVertices r n) x y) =
      P.connectedWithinSet (E.rightHalfPlaneVertices r) x y := by
  ext omega
  constructor
  · intro homega
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp homega
    exact P.connectedWithinSet_mono_region
      (E.rightHalfPlaneStripVertices_subset r n) x y hn
  · intro homega
    obtain ⟨n, hn⟩ :=
      E.connectedWithin_rightHalfPlane_exists_strip omega r x y homega
    exact Set.mem_iUnion.2 ⟨n, hn⟩

theorem PeriodicPlaneEmbedding.setConnectionWithin_rightHalfPlaneStrip_mono
    (E : PeriodicPlaneEmbedding P) (r : Real) (S T : Set V) :
    Monotone (fun n : Nat => P.setConnectionWithin
      (E.rightHalfPlaneStripVertices r n) S T) := by
  intro n N hnN
  exact P.setConnectionWithin_mono_region
    (E.rightHalfPlaneStripVertices_mono r hnN) S T

theorem PeriodicPlaneEmbedding.iUnion_setConnectionWithin_rightHalfPlaneStrip
    (E : PeriodicPlaneEmbedding P) (r : Real) (S T : Set V) :
    (⋃ n : Nat, P.setConnectionWithin
        (E.rightHalfPlaneStripVertices r n) S T) =
      P.setConnectionWithin (E.rightHalfPlaneVertices r) S T := by
  ext omega
  constructor
  · intro homega
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp homega
    exact P.setConnectionWithin_mono_region
      (E.rightHalfPlaneStripVertices_subset r n) S T hn
  · rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨n, hn⟩ :=
      E.connectedWithin_rightHalfPlane_exists_strip omega r x y hxy
    exact Set.mem_iUnion.2 ⟨n, x, hx, y, hy, hn⟩

theorem PeriodicPlaneEmbedding.rightHalfPlaneStrip_connection_measureReal_tendsto
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (S T : Set V) :
    Tendsto (fun n : Nat => mu.real (P.setConnectionWithin
      (E.rightHalfPlaneStripVertices r n) S T)) atTop
      (nhds (mu.real
        (P.setConnectionWithin (E.rightHalfPlaneVertices r) S T))) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
    (E.setConnectionWithin_rightHalfPlaneStrip_mono r S T)
  rw [E.iUnion_setConnectionWithin_rightHalfPlaneStrip r S T] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure


end StatMech.FK.PeriodicPlanar
