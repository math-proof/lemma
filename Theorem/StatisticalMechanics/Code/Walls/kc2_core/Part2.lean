/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
import Theorem.StatisticalMechanics.Code.Walls.kc2_supportisface
import Theorem.StatisticalMechanics.Code.Walls.kc2_dartdircases
import Theorem.StatisticalMechanics.Code.Walls.kc2_rightfaceinK
import Theorem.StatisticalMechanics.Code.Walls.kc2_downfaceoutK
import Theorem.StatisticalMechanics.Code.Walls.kc2_leftupfacecell.Part2
import Def.StatisticalMechanics.Code.Walls.kc2_core
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem kc2_supportOddNonRight_of_core {K : Set (Site 2)} {a : {e : Dart // IsBoundaryDart K e}}
    (h : exc_SupportOddInK K a) : kc2_SupportOddNonRight K a :=
  fun z hz hodd _e _he _hzf _hdir => h z hz hodd


theorem kc2_supportOddInK_of_nonRight {K : Set (Site 2)} {a : {e : Dart // IsBoundaryDart K e}}
    (h : kc2_SupportOddNonRight K a) : exc_SupportOddInK K a := by
  intro z hz hodd
  obtain ⟨i, hzf, hbd⟩ := kc2_support_is_face_exists K a hz
  
  set e : Dart := (dartNext K)^[i] a.1 with he_def
  rcases kc2_dart_dir_cases e with hdir | hdir | hdir | hdir
  · 
    rw [hzf]; exact kc2_supportOdd_right hbd hdir
  · 
    exact h z hz hodd e hbd hzf (Or.inr (Or.inr hdir))
  · 
    exact h z hz hodd e hbd hzf (Or.inr (Or.inl hdir))
  · 
    exact h z hz hodd e hbd hzf (Or.inl hdir)


theorem kc2_supportOddInK_iff_nonRight {K : Set (Site 2)} {a : {e : Dart // IsBoundaryDart K e}} :
    exc_SupportOddInK K a ↔ kc2_SupportOddNonRight K a :=
  ⟨kc2_supportOddNonRight_of_core, kc2_supportOddInK_of_nonRight⟩


theorem kc2_down_residue_is_evenRay {K : Set (Site 2)} {a : {e : Dart // IsBoundaryDart K e}}
    {e : Dart} (he : IsBoundaryDart K e) (hd : e.dir = ![0, -1]) :
    (¬ Even (jec_rayCount (dartFace e) (mpl_orbitLoop K a)) → dartFace e ∈ K) ↔
      Even (jec_rayCount (dartFace e) (mpl_orbitLoop K a)) := by
  constructor
  · intro himp
    by_contra hodd
    exact kc2_dartFace_down_notMem he hd (himp hodd)
  · intro heven hodd
    exact absurd heven hodd


end Walls
end StatMech
