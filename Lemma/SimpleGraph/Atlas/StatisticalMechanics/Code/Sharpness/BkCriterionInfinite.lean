import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite
open MeasureTheory Set Finset StatMech StatMech.Sharpness


/--
[shk_mem_boundaryEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInfinite.lean)
-/
@[path]
private lemma shk_mem_boundaryEdges_iff_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {x y : Site d} :
-- imply
  (x, y) ∈ boundaryEdges d S ↔ x ∈ S ∧ y ∉ S ∧ (hypercubicLattice d).Adj x y := by
-- proof
  apply StatMech.Sharpness.shk_mem_boundaryEdges_iff

/--
[shk_firstExit_inclusion_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInfinite.lean)
-/
@[path]
private lemma shk_firstExit_inclusion_lattice_eq
  {d : ℕ}
  {A : Set (Site d)}
  {S : Finset (Site d)}
  {B : Set (Site d)}
  {u : Site d}
-- given
  (huS : u ∈ S)
  (hBS : ∀ z ∈ B, z ∉ S) :
-- imply
  connEvent (hypercubicLattice d) A u B ⊆ ⋃ q ∈ boundaryEdges d S, disjointOccurrence (connEvent (hypercubicLattice d) (S : Set (Site d)) u {q.1}) (disjointOccurrence (edgeOpenEvent q.1 q.2) (connEvent (hypercubicLattice d) A q.2 B)) := by
-- proof
  apply StatMech.Sharpness.shk_firstExit_inclusion_lattice A S B u huS hBS

/--
[shk_connEvent_singleton_eq_connWithinEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInfinite.lean)
-/
@[path]
private lemma shk_connEvent_singleton_eq_connWithinEvent_eq
  {d : ℕ}
  {T : Set (Site d)}
  {u x : Site d} :
-- imply
  connEvent (hypercubicLattice d) T u {x} = connWithinEvent d T u x := by
-- proof
  apply StatMech.Sharpness.shk_connEvent_singleton_eq_connWithinEvent T u x

/--
[shk_connEvent_singleton_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInfinite.lean)
-/
@[path]
private lemma shk_connEvent_singleton_dependsOn_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {u x : Site d} :
-- imply
  DependsOn (connEvent (hypercubicLattice d) (T : Set (Site d)) u {x}) (internalEdgesFinset T : Set (Sym2 (Site d))) := by
-- proof
  apply StatMech.Sharpness.shk_connEvent_singleton_dependsOn T u x

/--
[shk_edgeOpenEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInfinite.lean)
-/
@[path]
private lemma shk_edgeOpenEvent_dependsOn_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  DependsOn (edgeOpenEvent x y) ({s(x, y)} : Set (Sym2 (Site d))) := by
-- proof
  apply StatMech.Sharpness.shk_edgeOpenEvent_dependsOn x y

/--
[bk_criterion_infinite_lattice_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInfinite.lean)
-/
@[path]
private lemma bk_criterion_infinite_lattice_singleton_eq
  {d : ℕ}
  {Lam S : Finset (Site d)}
  {u x : Site d}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (huS : u ∈ S)
  (hxS : x ∉ S) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (connEvent (hypercubicLattice d) (Lam : Set (Site d)) u {x}) ≤ ∑ q ∈ boundaryEdges d S, (p : ℝ) * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (connEvent (hypercubicLattice d) (S : Set (Site d)) u {q.1}) * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (connEvent (hypercubicLattice d) (Lam : Set (Site d)) q.2 {x}) := by
-- proof
  apply StatMech.Sharpness.bk_criterion_infinite_lattice_singleton p hp Lam S u x huS hxS


-- created on 2026-10-23
