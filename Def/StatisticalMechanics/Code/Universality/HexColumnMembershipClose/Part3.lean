/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexColumnMembershipClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexColumnMembershipClose.Part3


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


def hcm_CutReaches (h0 : ℤ) (T : ℕ) (memD : List ℤ → Prop) : Prop :=
  ∀ d : {ts // memD ts},
    (T : ℝ) ≤ hexW2_partialDisp h0 d.1 (hexW2_cutPos h0 d.1) - (HexWalk.halfStep h0).re


def hcm_DropDescends (h0 : ℤ) (T : ℕ) (memD : List ℤ → Prop) : Prop :=
  ∀ d : {ts // memD ts},
    (T : ℝ)
      ≤ (HexWalk.halfStep (hexInfra_headAccum h0 (d.1.take (hexW2_cutPos h0 d.1)))).re
        - (hexInfra_stepReSum (hexInfra_headAccum h0 (d.1.take (hexW2_cutPos h0 d.1)))
              (d.1.drop (hexW2_cutPos h0 d.1))
            + (HexWalk.halfStep
                (hexInfra_headAccum (hexInfra_headAccum h0 (d.1.take (hexW2_cutPos h0 d.1)))
                  (d.1.drop (hexW2_cutPos h0 d.1)))).re)


def hcm_halvesInColumn_of_descends (a0 : ℂ) (h0 : ℤ) (T : ℕ) (memD : List ℤ → Prop)
    (hreach : hcm_CutReaches h0 T memD)
    (hdesc : hcm_DropDescends h0 T memD) :
    HexHalvesInColumn h0 memD (hcm_BridgeContent a0 T) where
  htake := fun d => ⟨h0, hcm_take_spans a0 h0 T d.1 (hexW2_cutPos h0 d.1) (hreach d)⟩
  hdrop := fun d => by
    refine ⟨hfs_stHead h0 (d.1.take (hexW2_cutPos h0 d.1)), ?_⟩
    
    
    have hspan := hcm_drop_spans a0 h0 T d.1 (hexW2_cutPos h0 d.1) (hdesc d)
    exact (hcm_spans_transl (hfs_stMid a0 h0 (d.1.take (hexW2_cutPos h0 d.1))) a0
      (hfs_stHead h0 (d.1.take (hexW2_cutPos h0 d.1))) T
      (d.1.drop (hexW2_cutPos h0 d.1))).mp hspan


noncomputable def hcm_halfClass_of_descends (a0 : ℂ) (h0 : ℤ) (x : ℝ) (T : ℕ)
    (memD : List ℤ → Prop)
    (hreach : hcm_CutReaches h0 T memD) (hdesc : hcm_DropDescends h0 T memD) :
    HexHalfClass a0 h0 x memD (hcm_BridgeContent a0 T) :=
  hhe_halfClass_of_halves a0 h0 x memD (hcm_BridgeContent a0 T)
    (hcm_halvesInColumn_of_descends a0 h0 T memD hreach hdesc)


end StatMech.Universality
