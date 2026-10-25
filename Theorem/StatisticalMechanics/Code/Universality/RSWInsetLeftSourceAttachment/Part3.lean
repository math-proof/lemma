/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetLeftSourceAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWInsetSourceAttachment.Part2
import Def.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment.Part4
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_insetLeftSourceCore_to_strictAxis_mass (p : NNReal) (hp:p≤1) (n : Int) :
    (p : Real)*(bernoulliProductMeasure (E :=Sym2 (Site 2)) p hp).real (rlc_insetLeftSourceCoreEvent n) ≤
      (bernoulliProductMeasure (E :=Sym2 (Site 2)) p hp).real
        (rlc_strictAxisLeftSourceEvent n) := by
  let I:=RlcInsetLeftSourcePath n
  let N:=Fintype.card I
  let path : Fin N → I := (Fintype.equivFin I).symm
  let W : Fin N → Set (ConfigSpace (Sym2 (Site 2))) := fun i=>rlc_pathOpen (path i).1
  let X : Fin N → Set (ConfigSpace (Sym2 (Site 2))) := fun i=>{w|w (rlc_insetLeftAttachmentEdge (path i)) = true}
  let T : Fin N → Finset (Sym2 (Site 2)) := fun i=>rlc_pathEdges (path i).1
  let U : Fin N → Finset (Sym2 (Site 2)) := fun i=>{rlc_insetLeftAttachmentEdge (path i)}
  have hcover:(⋃i,W i)=rlc_insetLeftSourceCoreEvent n := by
    rw [rlc_insetLeftSourceCoreEvent,←rlc_iUnion_restrictedPathOpen]
    ext w
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      refine ⟨path i,?_⟩
      simpa [W] using hi
    · rintro ⟨g,hg⟩
      refine ⟨Fintype.equivFin I g,?_⟩
      simpa [W,path] using hg
  rw [←hcover]
  apply rlc_exploration_lower_bound p hp W X T U
    (rlc_strictAxisLeftSourceEvent n) (p : Real)
  · exact_mod_cast p.2
  · intro i; exact rlc_pathOpen_dependsOn (path i).1
  · intro i; simpa [X,U] using coord_true_dependsOn (rlc_insetLeftAttachmentEdge (path i))
  · intro i
    rw [Finset.disjoint_left]
    intro e ht hu
    have he:e=rlc_insetLeftAttachmentEdge (path i):=by simpa [U] using hu
    subst e
    simp only [rlc_exploredSupport,Finset.mem_biUnion,
      Finset.mem_filter,Finset.mem_univ,true_and] at ht
    obtain ⟨j,_hji,hj⟩:=ht
    exact rlc_insetLeftAttachmentEdge_not_mem_pathEdges (path i) (path j) hj
  · intro i
    simpa [X] using (coord_true_prob (E :=Sym2 (Site 2)) p hp (rlc_insetLeftAttachmentEdge (path i))).ge
  · intro i w hw
    have hg:w∈rlc_pathOpen (path i).1 := (rlc_mem_firstWitness_iff.mp hw.1).1
    have ho:=rlc_insetLeftAttachedPath_open (path i) hg hw.2
    apply Set.mem_iUnion.mpr
    exact ⟨⟨rlc_insetLeftAttachedPath (path i),rlc_insetLeftAttachedPath_axis_strict (path i)⟩,ho⟩

end
end StatMech.Universality
