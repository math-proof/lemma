import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc83downstreamaudit
open MeasureTheory Finset StatMech


/--
[rc83_bk_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc83downstreamaudit.lean)
-/
@[path]
private lemma rc83_bk_increasing_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (hp : p ≤ 1)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.rc83_bk_increasing hp hA hB

/--
[rc83_disjointOccurrence_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc83downstreamaudit.lean)
-/
@[path]
private lemma rc83_disjointOccurrence_increasing_eq
  {A B : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  IsIncreasing (disjointOccurrence A B) := by
-- proof
  apply StatMech.rc83_disjointOccurrence_increasing hA hB

/--
[rc83_bk_triple_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc83downstreamaudit.lean)
-/
@[path]
private lemma rc83_bk_triple_increasing_eq
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
  apply StatMech.rc83_bk_triple_increasing hp hP hQ hR

/--
[rc83_reimer_not_needed_for_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc83downstreamaudit.lean)
-/
@[path]
private lemma rc83_reimer_not_needed_for_increasing_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (hp : p ≤ 1)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.rc83_reimer_not_needed_for_increasing hp hA hB

/--
[rc83_reimer_core_of_increasing_would_follow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc83downstreamaudit.lean)
-/
@[path]
private lemma rc83_reimer_core_of_increasing_would_follow_eq
  {n : ℕ}
  {φ : Fin n → Bool → ℝ}
  {A B : Set (ConfigSpace (Fin n))}
-- given
  (hφ0 : ∀ i b, 0 ≤ φ i b)
  (hφ1 : ∀ i, φ i false + φ i true = 1)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.rc83_reimer_core_of_increasing_would_follow n φ hφ0 hφ1 A B hA hB

/--
[rc83_connEvent_triple_increasing_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc83downstreamaudit.lean)
-/
@[path]
private lemma rc83_connEvent_triple_increasing_witness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Set V}
  {u : V}
  {x y : V}
  {A B : Set V} :
-- imply
  IsIncreasing (disjointOccurrence (connEvent G S u {x}) (disjointOccurrence (edgeOpenEvent x y) (connEvent G A y B))) := by
-- proof
  apply StatMech.rc83_connEvent_triple_increasing_witness G S u x y A B

/--
[rc83_downstream_audit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc83downstreamaudit.lean)
-/
@[path]
private lemma rc83_downstream_audit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {p : ℝ≥0}
  {S : Set V}
  {u : V}
  {x y : V}
  {A B : Set V}
-- given
  (hp : p ≤ 1) :
-- imply
  (∀ (P Q R : Set (ConfigSpace (Sym2 V))), IsIncreasing P → IsIncreasing Q → IsIncreasing R → (bernoulliProductMeasure (E := Sym2 V) p hp).real (disjointOccurrence P (disjointOccurrence Q R)) ≤ (bernoulliProductMeasure (E := Sym2 V) p hp).real P * (bernoulliProductMeasure (E := Sym2 V) p hp).real Q * (bernoulliProductMeasure (E := Sym2 V) p hp).real R) ∧ IsIncreasing (disjointOccurrence (connEvent G S u {x}) (disjointOccurrence (edgeOpenEvent x y) (connEvent G A y B))) := by
-- proof
  apply StatMech.rc83_downstream_audit G hp S u x y A B


-- created on 2026-10-23
