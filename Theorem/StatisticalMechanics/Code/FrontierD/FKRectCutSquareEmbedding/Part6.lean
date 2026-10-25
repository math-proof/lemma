/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part5
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
import Def.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part5
open MeasureTheory StatMech.Lattice SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPrimalUnexploredRightArmEvent_isIncreasing
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (source : FKRectPrimalUnexploredVertex R S eta) :
    IsIncreasing
      (FKRectPrimalUnexploredRightArmEvent R S eta source) := by
  intro omega omega' homega
  rintro ⟨target, hright, hreach⟩
  exact ⟨target, hright,
    hreach.mono (FK.openSub_mono _ homega)⟩


theorem fkRectPrimalUnexplored_reachable_box
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (rho : ConfigSpace
      (Sym2 (FK.boxVerts 2 (R.width + R.height))))
    {x y : FKRectPrimalUnexploredVertex R S eta}
    (hreach :
      (FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta)
        (FK.ocd_innerRestrict
          (fkRectPrimalUnexploredBoxEmbedding R S eta) rho)).Reachable x y) :
    (FK.openSub (FK.boxGraph 2 (R.width + R.height)) rho).Reachable
      (fkRectPrimalUnexploredBoxEmbedding R S eta x)
      (fkRectPrimalUnexploredBoxEmbedding R S eta y) := by
  let f :
      FK.openSub (fkRectPrimalUnexploredInducedGraph R S eta)
          (FK.ocd_innerRestrict
            (fkRectPrimalUnexploredBoxEmbedding R S eta) rho) →g
        FK.openSub (FK.boxGraph 2 (R.width + R.height)) rho :=
    { toFun := fkRectPrimalUnexploredBoxEmbedding R S eta
      map_rel' := fun {x y} hxy => by
        refine ⟨(fkRectPrimalUnexplored_boxAdjMatch R S eta x y).mp hxy.1, ?_⟩
        simpa [FK.ocd_innerRestrict, FK.ocd_innerEdge_mk] using hxy.2 }
  exact hreach.map f


theorem fkRectPrimalUnexplored_rightArmCylinder_subset_boxConnections
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (source : FKRectPrimalUnexploredVertex R S eta) :
    FK.boxRestrict 2 (R.width + R.height) ⁻¹'
        (FK.ocd_innerRestrict
          (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹'
            FKRectPrimalUnexploredRightArmEvent R S eta source) ⊆
      ⋃ target : FKRectPrimalUnexploredVertex R S eta,
        ⋃ _ : target.1.1 = fkRectRightColumn R,
          FK.boxConnEvent 2 (R.width + R.height)
            (fkRectPrimalUnexploredBoxEmbedding R S eta source)
            (fkRectPrimalUnexploredBoxEmbedding R S eta target) := by
  intro omega homega
  rcases homega with ⟨target, hright, hreach⟩
  simp only [Set.mem_iUnion]
  refine ⟨target, hright, ?_⟩
  exact fkRectPrimalUnexplored_reachable_box R S eta
    (FK.boxRestrict 2 (R.width + R.height) omega) hreach


theorem fkRectLeftRightSquareDisplacement_not_mem_box
    (R : FKRectTorus) (i z : Fin R.height) :
    -fkRectVertexSquareSite R (fkRectLeftColumn R, i) +
        fkRectVertexSquareSite R (fkRectRightColumn R, z) ∉
      box 2 (R.width - 2) := by
  let du : Int :=
    (fkRectVertexSquareSite R (fkRectRightColumn R, z) 0) -
      fkRectVertexSquareSite R (fkRectLeftColumn R, i) 0
  let dv : Int :=
    (fkRectVertexSquareSite R (fkRectRightColumn R, z) 1) -
      fkRectVertexSquareSite R (fkRectLeftColumn R, i) 1
  have hsum : (2 : Int) * R.width - 3 ≤ du + dv := by
    dsimp [du, dv, fkRectVertexSquareSite, fkRectVertexSquarePoint,
      fkRectSquareSiteOfPair, fkRectSquareDevelopPoint,
      fkRectLeftColumn, fkRectRightColumn]
    have hi := i.isLt
    have hz := z.isLt
    have hw := R.width_gt_two
    omega
  intro hbox
  have h0 := hbox (0 : Fin 2)
  have h1 := hbox (1 : Fin 2)
  have h0' : du.natAbs ≤ R.width - 2 := by
    dsimp [du]
    simpa only [Pi.add_apply, Pi.neg_apply, sub_eq_add_neg, add_comm] using h0
  have h1' : dv.natAbs ≤ R.width - 2 := by
    dsimp [dv]
    simpa only [Pi.add_apply, Pi.neg_apply, sub_eq_add_neg, add_comm] using h1
  have h0Int : (du.natAbs : Int) ≤ (R.width - 2 : Nat) := by
    exact_mod_cast h0'
  have h1Int : (dv.natAbs : Int) ≤ (R.width - 2 : Nat) := by
    exact_mod_cast h1'
  have hdu : du ≤ (du.natAbs : Int) := Int.le_natAbs
  have hdv : dv ≤ (dv.natAbs : Int) := Int.le_natAbs
  have hw := R.width_gt_two
  omega


theorem fkRectBox_reachable_global
    (N : Nat) (omega : ConfigSpace (Sym2 (Site 2)))
    {x y : FK.boxVerts 2 N}
    (hreach :
      (FK.openSub (FK.boxGraph 2 N) (FK.boxRestrict 2 N omega)).Reachable
        x y) :
    Connected 2 omega x.1 y.1 := by
  let f :
      FK.openSub (FK.boxGraph 2 N) (FK.boxRestrict 2 N omega) →g
        openSubgraph 2 omega :=
    { toFun := Subtype.val
      map_rel' := fun {x y} hxy => by
        refine ⟨hxy.1, ?_⟩
        simpa [FK.boxRestrict, FK.edgeIncl, FK.ocd_innerEdge_mk] using hxy.2 }
  exact hreach.map f


theorem fkRectPrimalUnexplored_rightArmCylinder_subset_shift_boxBdry
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (source : FKRectPrimalUnexploredVertex R S eta)
    (hleft : source.1.1 = fkRectLeftColumn R) :
    let sourceSite :=
      (fkRectPrimalUnexploredBoxEmbedding R S eta source).1
    let g : Multiplicative (Site 2) := Multiplicative.ofAdd (-sourceSite)
    FK.boxRestrict 2 (R.width + R.height) ⁻¹'
        (FK.ocd_innerRestrict
          (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹'
            FKRectPrimalUnexploredRightArmEvent R S eta source) ⊆
      (ConfigSpace.shift g) ⁻¹' FK.boxBdryConnEvent 2 (R.width - 2) := by
  dsimp only
  intro omega homega
  rcases homega with ⟨target, hright, hreach⟩
  have hboxReach := fkRectPrimalUnexplored_reachable_box R S eta
    (FK.boxRestrict 2 (R.width + R.height) omega) hreach
  have hconn := fkRectBox_reachable_global
    (R.width + R.height) omega hboxReach
  let sourceSite : Site 2 :=
    (fkRectPrimalUnexploredBoxEmbedding R S eta source).1
  let targetSite : Site 2 :=
    (fkRectPrimalUnexploredBoxEmbedding R S eta target).1
  let g : Multiplicative (Site 2) := Multiplicative.ofAdd (-sourceSite)
  have hs : sourceSite =
      fkRectVertexSquareSite R (fkRectLeftColumn R, source.1.2) := by
    change fkRectVertexSquareSite R source.1 = _
    rw [show source.1 = (fkRectLeftColumn R, source.1.2) from
      Prod.ext hleft rfl]
  have ht : targetSite =
      fkRectVertexSquareSite R (fkRectRightColumn R, target.1.2) := by
    change fkRectVertexSquareSite R target.1 = _
    rw [show target.1 = (fkRectRightColumn R, target.1.2) from
      Prod.ext hright rfl]
  have hgsource : g • sourceSite = StatMech.Percolation.origin 2 := by
    funext j
    simp [g, StatMech.Percolation.smul_site_apply,
      StatMech.Percolation.origin]
  have hshiftConn :
      StatMech.Lattice.Connected 2 (ConfigSpace.shift g omega)
        (StatMech.Percolation.origin 2) (g • targetSite) := by
    rw [← hgsource]
    exact (StatMech.Percolation.connected_shift
      g omega sourceSite targetSite).2 hconn
  have houtside : g • targetSite ∉ box 2 (R.width - 2) := by
    have hout := fkRectLeftRightSquareDisplacement_not_mem_box
      R source.1.2 target.1.2
    rw [← hs, ← ht] at hout
    simpa [g, StatMech.Percolation.smul_site_apply] using hout
  exact FK.connectionEvent_subset_boxBdryConnEvent
    (R.width - 2) (by have := R.width_gt_two; omega : 1 ≤ R.width - 2)
    (g • targetSite) houtside hshiftConn


theorem fkRectPrimalUnexploredRightArm_freeMass_le_boxBdry
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (source : FKRectPrimalUnexploredVertex R S eta)
    (hleft : source.1.1 = fkRectLeftColumn R)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (∑ omega,
        (FKRectPrimalUnexploredRightArmEvent R S eta source).indicator
            (fun _ => (1 : Real)) omega *
          FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta)
            p q omega) ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2)) := by
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq)
  let sourceSite :=
    (fkRectPrimalUnexploredBoxEmbedding R S eta source).1
  let g : Multiplicative (Site 2) := Multiplicative.ofAdd (-sourceSite)
  let C := FK.boxRestrict 2 (R.width + R.height) ⁻¹'
    (FK.ocd_innerRestrict
      (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹'
        FKRectPrimalUnexploredRightArmEvent R S eta source)
  have hdomain := fkRectPrimalUnexplored_freeEvent_le_freeInfinite
    R S eta hp hp1 hq
      (fkRectPrimalUnexploredRightArmEvent_isIncreasing R S eta source)
  have hsubset : C ⊆
      (ConfigSpace.shift g) ⁻¹' FK.boxBdryConnEvent 2 (R.width - 2) := by
    simpa [C, sourceSite, g] using
      (fkRectPrimalUnexplored_rightArmCylinder_subset_shift_boxBdry
        R S eta source hleft)
  have hmono : mu.real C ≤
      mu.real ((ConfigSpace.shift g) ⁻¹'
        FK.boxBdryConnEvent 2 (R.width - 2)) :=
    measureReal_mono hsubset
  have hinv := FK.fkgqt_freeIV_isTranslationInvariant
    (d := 2) hp hp1 hq
  have hinvEvent := hinv.measure_preimage g
    (FK.isClopen_boxBdryConnEvent 2 (R.width - 2)).isOpen.measurableSet
  have hreal :
      mu.real ((ConfigSpace.shift g) ⁻¹'
          FK.boxBdryConnEvent 2 (R.width - 2)) =
        mu.real (FK.boxBdryConnEvent 2 (R.width - 2)) := by
    exact congrArg ENNReal.toReal hinvEvent
  exact hdomain.trans (hmono.trans_eq hreal)

end
end StatMech.FrontierD
