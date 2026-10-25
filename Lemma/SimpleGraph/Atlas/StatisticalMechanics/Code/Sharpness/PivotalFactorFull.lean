import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.PivotalFactorFull.Part3
open MeasureTheory Function Set StatMech StatMech.Sharpness


/--
[mem_internalEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorFull.lean)
-/
@[path]
private lemma mem_internalEdges_eq
  {d : ℕ}
  {S : Set (Site d)}
  {x y : Site d}
-- given
  (hx : x ∈ S)
  (hy : y ∈ S) :
-- imply
  s(x, y) ∈ internalEdges S := by
-- proof
  apply StatMech.Sharpness.mem_internalEdges hx hy

/--
[mem_internalEdgesFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorFull.lean)
-/
@[path]
private lemma mem_internalEdgesFinset_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {e : Sym2 (Site d)} :
-- imply
  e ∈ internalEdgesFinset S ↔ ∃ x ∈ S, ∃ y ∈ S, e = s(x, y) := by
-- proof
  apply StatMech.Sharpness.mem_internalEdgesFinset

/--
[internalEdgesFinset_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorFull.lean)
-/
@[path]
private lemma internalEdgesFinset_coe_eq
  {d : ℕ}
  {S : Finset (Site d)} :
-- imply
  (internalEdgesFinset S : Set (Sym2 (Site d))) = internalEdges (S : Set _) := by
-- proof
  apply StatMech.Sharpness.internalEdgesFinset_coe S

/--
[shp_internalEdges_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorFull.lean)
-/
@[path]
private lemma shp_internalEdges_disjoint_eq
  {d : ℕ}
  {S : Set (Site d)}
  {U : Set (Sym2 (Site d))}
-- given
  (hU : ∀ e ∈ U, ∃ a b : Site d, e = s(a, b) ∧ (a ∉ S ∨ b ∉ S)) :
-- imply
  Disjoint (internalEdges S) U := by
-- proof
  apply StatMech.Sharpness.shp_internalEdges_disjoint hU

/--
[shp_internalEdgesFinset_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorFull.lean)
-/
@[path]
private lemma shp_internalEdgesFinset_disjoint_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {U : Finset (Sym2 (Site d))}
-- given
  (hU : ∀ e ∈ U, ∃ a b : Site d, e = s(a, b) ∧ (a ∉ S ∨ b ∉ S)) :
-- imply
  Disjoint (internalEdgesFinset S) U := by
-- proof
  apply StatMech.Sharpness.shp_internalEdgesFinset_disjoint hU

/--
[shp_connWithin_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorFull.lean)
-/
@[path]
private lemma shp_connWithin_transfer_eq
  {d : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {S : Set (Site d)}
  {a b : ↥S}
-- given
  (hagree : ∀ e ∈ internalEdges S, ω e = ω' e)
  (h : ConnectedWithin d ω S a b) :
-- imply
  ConnectedWithin d ω' S a b := by
-- proof
  apply StatMech.Sharpness.shp_connWithin_transfer hagree h

/--
[shp_connWithinEvent_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorFull.lean)
-/
@[path]
private lemma shp_connWithinEvent_congr_eq
  {d : ℕ}
  {S : Set (Site d)}
  {o x : Site d}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (hagree : ∀ e ∈ internalEdges S, ω e = ω' e) :
-- imply
  ω ∈ connWithinEvent d S o x ↔ ω' ∈ connWithinEvent d S o x := by
-- proof
  apply StatMech.Sharpness.shp_connWithinEvent_congr hagree

/--
[shp_connWithinEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorFull.lean)
-/
@[path]
private lemma shp_connWithinEvent_dependsOn_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {o x : Site d} :
-- imply
  DependsOn ((connWithinEvent d (S : Set (Site d)) o x).indicator (fun _ => (1 : ℝ))) (internalEdgesFinset S : Set (Sym2 (Site d))) := by
-- proof
  apply StatMech.Sharpness.shp_connWithinEvent_dependsOn

/--
[shp_connWithin_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorFull.lean)
-/
@[path]
private lemma shp_connWithin_factor_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {o x : Site d}
  {B : Set (ConfigSpace (Sym2 (Site d)))}
  {U : Finset (Sym2 (Site d))}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hdisj : Disjoint (internalEdgesFinset S) U)
  (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set (Sym2 (Site d)))) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (connWithinEvent d (S : Set (Site d)) o x ∩ B) = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (connWithinEvent d (S : Set (Site d)) o x) * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real B := by
-- proof
  apply StatMech.Sharpness.shp_connWithin_factor p hp S o x B U hdisj hB

/--
[shp_pivotal_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorFull.lean)
-/
@[path]
private lemma shp_pivotal_factor_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {o x : Site d}
  {B : Set (ConfigSpace (Sym2 (Site d)))}
  {U : Finset (Sym2 (Site d))}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hUext : ∀ e ∈ U, ∃ a b : Site d, e = s(a, b) ∧ (a ∉ (S : Set (Site d)) ∨ b ∉ (S : Set (Site d))))
  (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set (Sym2 (Site d)))) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (connWithinEvent d (S : Set (Site d)) o x ∩ B) = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (connWithinEvent d (S : Set (Site d)) o x) * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real B := by
-- proof
  apply StatMech.Sharpness.shp_pivotal_factor p hp S o x B U hUext hB


-- created on 2026-10-23
