import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment.Part3
open Finset SimpleGraph Set MeasureTheory StatMech StatMech.Universality


/--
[rlc_insetLeftHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetLeftSourceAttachment.lean)
-/
@[path]
private lemma rlc_insetLeftHom_injective_eq
  {n : Int} :
-- imply
  Function.Injective (rlc_insetLeftHom n) := by
-- proof
  apply StatMech.Universality.rlc_insetLeftHom_injective n

/--
[rlc_insetLeftAttachmentEdge_not_mem_pathEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetLeftSourceAttachment.lean)
-/
@[path]
private lemma rlc_insetLeftAttachmentEdge_not_mem_pathEdges_eq
  {n : Int}
  {gamma delta : RlcInsetLeftSourcePath n} :
-- imply
  rlc_insetLeftAttachmentEdge gamma ∉ rlc_pathEdges delta.1 := by
-- proof
  apply StatMech.Universality.rlc_insetLeftAttachmentEdge_not_mem_pathEdges gamma delta

/--
[rlc_insetLeftAttachedPath_pathEdges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetLeftSourceAttachment.lean)
-/
@[path]
private lemma rlc_insetLeftAttachedPath_pathEdges_subset_eq
  {n : Int}
  {gamma : RlcInsetLeftSourcePath n} :
-- imply
  rlc_pathEdges (rlc_insetLeftAttachedPath gamma).1 ⊆ insert (rlc_insetLeftAttachmentEdge gamma) (rlc_pathEdges gamma.1) := by
-- proof
  apply StatMech.Universality.rlc_insetLeftAttachedPath_pathEdges_subset gamma

/--
[rlc_insetLeftAttachedPath_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetLeftSourceAttachment.lean)
-/
@[path]
private lemma rlc_insetLeftAttachedPath_open_eq
  {n : Int}
  {gamma : RlcInsetLeftSourcePath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hg : omega ∈ rlc_pathOpen gamma.1)
  (he : omega (rlc_insetLeftAttachmentEdge gamma) = true) :
-- imply
  omega ∈ rlc_pathOpen (rlc_insetLeftAttachedPath gamma).1 := by
-- proof
  apply StatMech.Universality.rlc_insetLeftAttachedPath_open gamma hg he

/--
[rlc_insetLeftAttachedPath_axis_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetLeftSourceAttachment.lean)
-/
@[path]
private lemma rlc_insetLeftAttachedPath_axis_strict_eq
  {n : Int}
  {gamma : RlcInsetLeftSourcePath n} :
-- imply
  ∀ {z:Site 2}, z ∈ rlc_pathVertices (rlc_insetLeftAttachedPath gamma).1 -> z 0=0 -> 0<z 1 := by
-- proof
  apply StatMech.Universality.rlc_insetLeftAttachedPath_axis_strict gamma

/--
[rlc_insetLeftSourceCore_to_strictAxis_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetLeftSourceAttachment.lean)
-/
@[path]
private lemma rlc_insetLeftSourceCore_to_strictAxis_mass_eq
  {p : NNReal}
  {n : Int}
-- given
  (hp:p≤1) :
-- imply
  (p : Real)*(bernoulliProductMeasure (E :=Sym2 (Site 2)) p hp).real (rlc_insetLeftSourceCoreEvent n) ≤ (bernoulliProductMeasure (E :=Sym2 (Site 2)) p hp).real (rlc_strictAxisLeftSourceEvent n) := by
-- proof
  apply StatMech.Universality.rlc_insetLeftSourceCore_to_strictAxis_mass p hp n


-- created on 2026-10-23
