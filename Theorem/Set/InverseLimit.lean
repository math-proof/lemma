module

public import Mathlib
public import Def.Topology.InverseLimit

public section

open InverseLimit


namespace InverseLimit

/--
[mem_carrier_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/InverseLimit.lean)
-/
public theorem mem_carrier_iff
  [Preorder ι]
  {X : ι → Type*}
  {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
  {x : ∀ i, X i} :
-- imply
  x ∈ carrier f ↔ ∀ ⦃i j : ι⦄ (h : i ≤ j), f h (x j) = x i :=
-- proof
  Iff.rfl

end InverseLimit

namespace InverseLimit

/--
[proj_compat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/InverseLimit.lean)
-/
public theorem proj_compat
  [Preorder ι]
  {X : ι → Type*}
  {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
  {x : ∀ i, X i}
-- given
  (hx : x ∈ carrier f) :
-- imply
  ι⦄ (h : i ≤ j) :
    f h (x j) = x i :=
-- proof
  hx h
variable [∀ i, TopologicalSpace (X i)]

end InverseLimit

namespace InverseLimit

/--
[isClosed_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/InverseLimit.lean)
-/
public theorem isClosed_carrier
  [Preorder ι]
  {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
-- given
  (hf : ∀ ⦃i j : ι⦄ (h : i ≤ j), Continuous (f h)) :
-- imply
  IsClosed (carrier f) := by
-- proof
  have heq : carrier f =
    ⋂ (i : ι) (j : ι) (h : i ≤ j), { x | f h (x j) = x i } := by
    ext x
    simp [carrier]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun h =>
    isClosed_eq ((hf h).comp (continuous_apply j)) (continuous_apply i)

end InverseLimit

namespace InverseLimit

/--
[isCompact_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/InverseLimit.lean)
-/
public theorem isCompact_carrier
  [Preorder ι]
  {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)]
  {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
-- given
  (hf : ∀ ⦃i j : ι⦄ (h : i ≤ j), Continuous (f h)) :
-- imply
  IsCompact (carrier f) :=
-- proof
  (isClosed_carrier hf).isCompact

end InverseLimit


-- created on 2026-10-20
-- updated on 2026-10-26
