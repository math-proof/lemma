import Mathlib
import sympy.Basic
import sympy.atlas.Topology.InverseLimit
open InverseLimit


/--
[mem_carrier_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/InverseLimit.lean)
-/
@[path]
private lemma mem_carrier_iff_eq
  [Preorder ι]
  {X : ι → Type*}
  {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
  {x : ∀ i, X i} :
-- imply
  x ∈ carrier f ↔ ∀ ⦃i j : ι⦄ (h : i ≤ j), f h (x j) = x i := by
-- proof
  apply InverseLimit.mem_carrier_iff

/--
[proj_compat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/InverseLimit.lean)
-/
@[path]
private lemma proj_compat_eq
  [Preorder ι]
  {X : ι → Type*}
  {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
  {x : ∀ i, X i}
-- given
  (hx : x ∈ carrier f) :
-- imply
  ι⦄ (h : i ≤ j) :
    f h (x j) = x i := by
-- proof
  apply InverseLimit.proj_compat hx

/--
[isClosed_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/InverseLimit.lean)
-/
@[path]
private lemma isClosed_carrier_eq
  [Preorder ι]
  {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
-- given
  (hf : ∀ ⦃i j : ι⦄ (h : i ≤ j), Continuous (f h)) :
-- imply
  IsClosed (carrier f) := by
-- proof
  apply InverseLimit.isClosed_carrier hf

/--
[isCompact_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/InverseLimit.lean)
-/
@[path]
private lemma isCompact_carrier_eq
  [Preorder ι]
  {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)]
  {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
-- given
  (hf : ∀ ⦃i j : ι⦄ (h : i ≤ j), Continuous (f h)) :
-- imply
  IsCompact (carrier f) := by
-- proof
  apply InverseLimit.isCompact_carrier hf


-- created on 2026-10-20
