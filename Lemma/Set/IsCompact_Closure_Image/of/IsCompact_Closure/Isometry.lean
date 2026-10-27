import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.ChamberCompactClosure
open Classical


/--
[isCompact_closure_image_of_isometry](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ChamberCompactClosure.lean)
-/
@[path]
lemma isCompact_closure_image_of_isometry
  [MetricSpace X]
  {f : X → X}
  {s : Set X}
-- given
  (hf : Isometry f)
  (hs : IsCompact (closure s)) :
-- imply
  IsCompact (closure (f '' s)) := by
-- proof
  have h1 : IsCompact (f '' closure s) := hs.image hf.continuous
  have h2 : closure (f '' s) ⊆ closure (f '' closure s) :=
    closure_mono (Set.image_mono subset_closure)
  rw [h1.isClosed.closure_eq] at h2
  exact h1.of_isClosed_subset isClosed_closure h2
section ChamberCompactClosure
variable {E : Type*} [MetricSpace E]
variable {W : Type*} [Group W]
variable (action : W → E → E)

/--
[chamber_compact_closure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ChamberCompactClosure.lean)
-/
@[path]
lemma chamber_compact_closure
  [MetricSpace E]
  [Group W]
  {action : W → E → E}
  {action}
  {σ : Set E}
  {w : W}
-- given
  (hiso : ActsByIsometries action)
  (hσ : IsCompact (closure σ)) :
-- imply
  IsCompact (closure (orbitSet action w σ)) :=
-- proof
  isCompact_closure_image_of_isometry (hiso w) hσ

/--
[chamber_isBounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ChamberCompactClosure.lean)
-/
@[path]
lemma chamber_isBounded
  [MetricSpace E]
  [Group W]
  {action : W → E → E}
  {action}
  {σ : Set E}
  {w : W}
-- given
  (hiso : ActsByIsometries action)
  (hσ : IsCompact (closure σ)) :
-- imply
  Bornology.IsBounded (orbitSet action w σ) :=
-- proof
  (chamber_compact_closure hiso hσ w).isBounded.subset subset_closure

/--
[chamber_diam_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ChamberCompactClosure.lean)
-/
@[path]
lemma chamber_diam_eq
  [MetricSpace E]
  [Group W]
  {action : W → E → E}
  {action}
  {σ : Set E}
  {w : W}
-- given
  (hiso : ActsByIsometries action) :
-- imply
  Metric.diam (orbitSet action w σ) = Metric.diam σ :=
-- proof
  (hiso w).diam_image σ
end ChamberCompactClosure


-- created on 2026-10-23
