import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterion.Part4
open MeasureTheory Finset StatMech StatMech.Sharpness


/--
[OccursOn.mono_config](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterion.lean)
-/
@[path]
private lemma mono_config_eq
  {A : Set (ConfigSpace E)}
  {K : Set E}
  {ω ω' : ConfigSpace E}
-- given
  (hA : IsIncreasing A)
  (h : ω ≤ ω')
  (hocc : OccursOn A K ω) :
-- imply
  OccursOn A K ω' := by
-- proof
  apply StatMech.Sharpness.OccursOn.mono_config hA h hocc

/--
[disjointOccurrence_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterion.lean)
-/
@[path]
private lemma disjointOccurrence_isIncreasing_eq
  {A B : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  IsIncreasing (disjointOccurrence A B) := by
-- proof
  apply StatMech.Sharpness.disjointOccurrence_isIncreasing hA hB

/--
[bk_triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterion.lean)
-/
@[path]
private lemma bk_triple_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {P Q R : Set (ConfigSpace E)}
-- given
  (hp : p ≤ 1)
  (hP : IsIncreasing P)
  (hQ : IsIncreasing Q)
  (hR : IsIncreasing R) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence P (disjointOccurrence Q R)) ≤ (bernoulliProductMeasure (E := E) p hp).real P * (bernoulliProductMeasure (E := E) p hp).real Q * (bernoulliProductMeasure (E := E) p hp).real R := by
-- proof
  apply StatMech.Sharpness.bk_triple hp hP hQ hR

/--
[bk_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterion.lean)
-/
@[path]
private lemma bk_criterion_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {s : Finset ι}
  {P Q R : ι → Set (ConfigSpace E)}
  {C : Set (ConfigSpace E)}
-- given
  (hp : p ≤ 1)
  (hP : ∀ i ∈ s, IsIncreasing (P i))
  (hQ : ∀ i ∈ s, IsIncreasing (Q i))
  (hR : ∀ i ∈ s, IsIncreasing (R i))
  (hC : C ⊆ ⋃ i ∈ s, disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real C ≤ ∑ i ∈ s, (bernoulliProductMeasure (E := E) p hp).real (P i) * (bernoulliProductMeasure (E := E) p hp).real (Q i) * (bernoulliProductMeasure (E := E) p hp).real (R i) := by
-- proof
  apply StatMech.Sharpness.bk_criterion hp s P Q R hP hQ hR hC

/--
[openSub_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterion.lean)
-/
@[path]
private lemma openSub_mono_eq
  {G : SimpleGraph V}
  {ω ω' : ConfigSpace (Sym2 V)}
-- given
  (h : ω ≤ ω') :
-- imply
  openSub G ω ≤ openSub G ω' := by
-- proof
  apply StatMech.Sharpness.openSub_mono G h

/--
[ConnWithin.mono_config](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterion.lean)
-/
@[path]
private lemma mono_config_eq_2
  {G : SimpleGraph V}
  {ω ω' : ConfigSpace (Sym2 V)}
  {A : Set V}
  {x y : A}
-- given
  (h : ω ≤ ω')
  (hc : ConnWithin G ω A x y) :
-- imply
  ConnWithin G ω' A x y := by
-- proof
  apply StatMech.Sharpness.ConnWithin.mono_config G h hc

/--
[isIncreasing_connEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterion.lean)
-/
@[path]
private lemma isIncreasing_connEvent_eq
  {G : SimpleGraph V}
  {A : Set V}
  {u : V}
  {B : Set V} :
-- imply
  IsIncreasing (connEvent G A u B) := by
-- proof
  apply StatMech.Sharpness.isIncreasing_connEvent G A u B

/--
[isIncreasing_edgeOpenEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterion.lean)
-/
@[path]
private lemma isIncreasing_edgeOpenEvent_eq
  {x y : V} :
-- imply
  IsIncreasing (edgeOpenEvent (V := V) x y) := by
-- proof
  apply StatMech.Sharpness.isIncreasing_edgeOpenEvent x y

/--
[bk_criterion_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterion.lean)
-/
@[path]
private lemma bk_criterion_conn_eq
  [Fintype V]
  [DecidableEq V]
  {p : ℝ≥0}
  {G : SimpleGraph V}
  {A S B : Set V}
  {u : V}
  {s : Finset ι}
  {boundaryPair : ι → V × V}
-- given
  (hp : p ≤ 1)
  (hincl : connEvent G A u B ⊆ ⋃ i ∈ s, disjointOccurrence (connEvent G S u {(boundaryPair i).1}) (disjointOccurrence (edgeOpenEvent (boundaryPair i).1 (boundaryPair i).2) (connEvent G A (boundaryPair i).2 B))) :
-- imply
  (bernoulliProductMeasure (E := Sym2 V) p hp).real (connEvent G A u B) ≤ ∑ i ∈ s, (bernoulliProductMeasure (E := Sym2 V) p hp).real (connEvent G S u {(boundaryPair i).1}) * (bernoulliProductMeasure (E := Sym2 V) p hp).real (edgeOpenEvent (boundaryPair i).1 (boundaryPair i).2) * (bernoulliProductMeasure (E := Sym2 V) p hp).real (connEvent G A (boundaryPair i).2 B) := by
-- proof
  apply StatMech.Sharpness.bk_criterion_conn hp G A S B u s boundaryPair hincl


-- created on 2026-10-23
