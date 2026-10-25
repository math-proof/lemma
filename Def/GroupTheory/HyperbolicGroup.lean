/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HyperbolicGroup.lean -/

import Mathlib.Geometry.Group.WordMetric
import Mathlib.GroupTheory.Finiteness
import Theorem.Topology.MetricSpace.GromovHyperbolic
import Lemma.Set.MetricSpace.GromovHyperbolic
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

end Group
