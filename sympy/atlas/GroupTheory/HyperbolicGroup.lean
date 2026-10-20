/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HyperbolicGroup.lean -/

import Mathlib.Geometry.Group.WordMetric
import Mathlib.GroupTheory.Finiteness
import sympy.atlas.Topology.MetricSpace.GromovHyperbolic
/-!
# Hyperbolic groups

This file defines word-hyperbolic finitely generated groups: a group is word-hyperbolic
when some finite generating family's word metric is Gromov-hyperbolic
(`MathlibExt.Topology.MetricSpace.GromovHyperbolic`).

## Main definitions

* `Group.IsHyperbolic G`: a group `G` is word-hyperbolic, i.e. it admits a finite generating
  family whose word metric (`Group.Generators.normedGroup`) makes `G` a Gromov-hyperbolic space.

## Main results

* `Group.IsHyperbolic.fg`: a word-hyperbolic group is finitely generated.
* `Group.IsHyperbolic.of_subsingleton`: a trivial (subsingleton) group is word-hyperbolic.

## References

* M. Gromov, *Hyperbolic groups*, in Essays in Group Theory, Math. Sci. Res. Inst. Publ. 8,
  Springer (1987), 75-263. Word-hyperbolic groups are defined via the word metric on the
  Cayley graph in §1.2.

## Tags

hyperbolic group, word metric, geometric group theory
-/

namespace Group

variable {G : Type*} [Group G]

/-- A group `G` is word-hyperbolic if it admits a finite generating family `P` whose word metric
`Group.Generators.normedGroup` makes `G` a Gromov `δ`-hyperbolic space for some `δ`. -/
def IsHyperbolic (G : Type*) [Group G] : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (P : Group.Generators G ι) (δ : ℝ),
    @Metric.IsDeltaHyperbolic G P.normedGroup.toMetricSpace.toPseudoMetricSpace δ

/-- A word-hyperbolic group is finitely generated. -/
theorem IsHyperbolic.fg (h : IsHyperbolic G) : Group.FG G := by
  obtain ⟨ι, hι, P, _, _⟩ := h
  letI := hι
  rw [Group.fg_iff]
  exact ⟨Set.range P.val, P.closure_eq_top, Set.finite_range P.val⟩

/-- A trivial (subsingleton) group is word-hyperbolic, witnessed by the empty generating family and
`δ = 0`. -/
theorem IsHyperbolic.of_subsingleton (G : Type*) [Group G] [Subsingleton G] : IsHyperbolic G := by
  refine ⟨Empty, inferInstance, ⟨Empty.elim, Subsingleton.elim _ _⟩, 0, le_refl 0, fun w x y z => ?_⟩
  rw [Subsingleton.elim x w, Subsingleton.elim y w, Subsingleton.elim z w, min_self, sub_zero]

end Group

/-! ### Examples -/

-- The trivial group is word-hyperbolic.
example {G : Type*} [Group G] [Subsingleton G] : Group.IsHyperbolic G :=
  Group.IsHyperbolic.of_subsingleton G
