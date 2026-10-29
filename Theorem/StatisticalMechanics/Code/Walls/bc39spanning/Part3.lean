/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc39spanning.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
import Def.StatisticalMechanics.Code.Walls.bc39spanning.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc39_armRealisation_of_cutGeometryFixed (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc39_ArmCutGeometryFixed ω n) : bc38_ArmRealisation ω n := by
  obtain ⟨b, hdata, hclauses⟩ := hgeo
  intro rank par hroot
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hpadj, _hprank⟩ := hroot x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hloc, hself, hfun⟩ := hclauses y (par y) hybox htriy hpadj
  refine ⟨hloc, hself, fun hxne => hfun x hxne ?_⟩
  intro hxy'; subst hxy'; exact hxy rfl


theorem bc39_parentFunneling_of_cutGeometryFixed (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc39_ArmCutGeometryFixed ω n) : bc37_ParentFunneling ω n :=
  bc38_parentFunneling_of_residues ω n (bc39_armAdjSpanning ω n)
    (bc39_armRealisation_of_cutGeometryFixed ω n hgeo)


theorem bc39_selfDownArm_of_cutGeometryFixed (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc39_ArmCutGeometryFixed ω n) : bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_parentFunneling ω n (bc39_parentFunneling_of_cutGeometryFixed ω n hgeo)


theorem bc39_Tcount_le_boundary_of_cutGeometryFixed (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hgeo : bc39_ArmCutGeometryFixed ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc36_Tcount_le_boundary_of_selfDownArm ω n hn (bc39_selfDownArm_of_cutGeometryFixed ω n hgeo)


theorem bc39_burton_keane_bernoulli_of_cutGeometryFixed (hd : 1 ≤ d) (p : NNReal)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc39_ArmCutGeometryFixed ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc36_burton_keane_bernoulli_of_selfDownArm hd p hp1 hp0
    (fun ω n hn => bc39_selfDownArm_of_cutGeometryFixed ω n (hgeo ω n hn)) htrif


theorem bc39_armCutGeometryFixed_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc39_ArmCutGeometryFixed ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro t s htbox htri _; exact absurd htri (hno t htbox)


theorem bc39_cutGeometryFixed_shadow_consistent (parNode bpar bself : ℕ)
    (hnode : parNode ≠ bself) (hbpar : bpar ≠ bself)
    (F : ℕ → Prop) (hF : ∀ w, F w → w ≠ bself) :
    ∃ up : ℕ → Prop,
      (¬ up bself ∧ up bpar) ∧
      (¬ up bself ∧ up parNode) ∧
      (∀ w, F w → up parNode ∧ up w) := by
  refine ⟨fun w => w ≠ bself, ⟨by simp, hbpar⟩, ⟨by simp, hnode⟩, ?_⟩
  intro w hw
  exact ⟨hnode, hF w hw⟩


theorem bc39_cutGeometryFixed_clauses_coexist (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (b : Site d → Site d) {t s : Site d} (_hadj : bc37_ArmAdjacent ω n t s)
    (hloc : ¬ Connected d (removeSite t ω) (b t) (b s))
    (hself : ¬ Connected d (removeSite t ω) (b t) s)
    (hfun : ∀ x, x ≠ s → x ≠ t → Connected d (removeSite t ω) (b x) s) :
    (¬ Connected d (removeSite t ω) (b t) (b s)) ∧
      (¬ Connected d (removeSite t ω) (b t) s) ∧
      (∀ x, x ≠ s → x ≠ t → Connected d (removeSite t ω) (b x) s) :=
  ⟨hloc, hself, hfun⟩

end StatMech.Walls
