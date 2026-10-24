import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.RSWInsetSourceAttachment
open Finset SimpleGraph Set MeasureTheory StatMech StatMech.Universality


/--
[rlc_insetRightHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceAttachment.lean)
-/
@[path]
private lemma rlc_insetRightHom_injective_eq
  {n : Int} :
-- imply
  Function.Injective (rlc_insetRightHom n) := by
-- proof
  apply StatMech.Universality.rlc_insetRightHom_injective n

/--
[rlc_insetRightAttachmentEdge_not_mem_pathEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceAttachment.lean)
-/
@[path]
private lemma rlc_insetRightAttachmentEdge_not_mem_pathEdges_eq
  {n : Int}
  {gamma delta : RlcInsetRightSourcePath n} :
-- imply
  rlc_insetRightAttachmentEdge gamma ∉ rlc_pathEdges delta.1 := by
-- proof
  apply StatMech.Universality.rlc_insetRightAttachmentEdge_not_mem_pathEdges gamma delta

/--
[rlc_insetRightAttachedPath_pathEdges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceAttachment.lean)
-/
@[path]
private lemma rlc_insetRightAttachedPath_pathEdges_subset_eq
  {n : Int}
  {gamma : RlcInsetRightSourcePath n} :
-- imply
  rlc_pathEdges (rlc_insetRightAttachedPath gamma).1 ⊆ insert (rlc_insetRightAttachmentEdge gamma) (rlc_pathEdges gamma.1) := by
-- proof
  apply StatMech.Universality.rlc_insetRightAttachedPath_pathEdges_subset gamma

/--
[rlc_insetRightAttachedPath_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceAttachment.lean)
-/
@[path]
private lemma rlc_insetRightAttachedPath_open_eq
  {n : Int}
  {gamma : RlcInsetRightSourcePath n}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hgamma : omega ∈ rlc_pathOpen gamma.1)
  (hattach : omega (rlc_insetRightAttachmentEdge gamma) = true) :
-- imply
  omega ∈ rlc_pathOpen (rlc_insetRightAttachedPath gamma).1 := by
-- proof
  apply StatMech.Universality.rlc_insetRightAttachedPath_open gamma hgamma hattach

/--
[rlc_insetRightAttachedPath_axis_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceAttachment.lean)
-/
@[path]
private lemma rlc_insetRightAttachedPath_axis_strict_eq
  {n : Int}
  {gamma : RlcInsetRightSourcePath n} :
-- imply
  ∀ {z : Site 2}, z ∈ rlc_pathVertices (rlc_insetRightAttachedPath gamma).1 -> z 0 = 0 -> z 1 < 0 := by
-- proof
  apply StatMech.Universality.rlc_insetRightAttachedPath_axis_strict gamma

/--
[rlc_insetRightSourceCore_to_strictAxis_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceAttachment.lean)
-/
@[path]
private lemma rlc_insetRightSourceCore_to_strictAxis_mass_eq
  {p : NNReal}
  {n : Int}
-- given
  (hp : p ≤ 1) :
-- imply
  (p : Real) * (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_insetRightSourceCoreEvent n) ≤ (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real (rlc_strictAxisRightSourceEvent n) := by
-- proof
  apply StatMech.Universality.rlc_insetRightSourceCore_to_strictAxis_mass p hp n


-- created on 2026-10-23
