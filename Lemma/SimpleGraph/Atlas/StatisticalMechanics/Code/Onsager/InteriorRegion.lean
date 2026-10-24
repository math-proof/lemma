import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.InteriorRegion
open StatMech StatMech.Onsager StatMech.Onsager.InteriorRegion


/--
[liftS_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean)
-/
@[path]
private lemma liftS_finite_eq
  {P : Finset Pt} :
-- imply
  (liftS P).Finite := by
-- proof
  apply StatMech.Onsager.InteriorRegion.liftS_finite P

/--
[mem_liftS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean)
-/
@[path]
private lemma mem_liftS_eq
  {P : Finset Pt}
  {q : Pt} :
-- imply
  toSite q ∈ liftS P ↔ q ∈ P := by
-- proof
  apply StatMech.Onsager.InteriorRegion.mem_liftS P q

/--
[mem_Lcells](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean)
-/
@[path]
private lemma mem_Lcells_eq
  {q : Pt} :
-- imply
  q ∈ Lcells ↔ (0 ≤ q.1 ∧ q.1 ≤ 3 ∧ 0 ≤ q.2 ∧ q.2 ≤ 3) ∧ ¬ (q.1 ≤ 1 ∧ q.2 ≤ 1) := by
-- proof
  apply StatMech.Onsager.InteriorRegion.mem_Lcells q

/--
[Lint_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean)
-/
@[path]
private lemma Lint_finite_eq :
-- imply
  Lint.Finite := by
-- proof
  apply StatMech.Onsager.InteriorRegion.Lint_finite

/--
[wReflex_not_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean)
-/
@[path]
private lemma wReflex_not_interior_eq :
-- imply
  toSite wReflex ∉ Lint := by
-- proof
  apply StatMech.Onsager.InteriorRegion.wReflex_not_interior

/--
[launch_pt_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean)
-/
@[path]
private lemma launch_pt_interior_eq :
-- imply
  toSite (wReflex.1 + 1, wReflex.2) ∈ Lint := by
-- proof
  apply StatMech.Onsager.InteriorRegion.launch_pt_interior

/--
[launch_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean)
-/
@[path]
private lemma launch_interior_eq :
-- imply
  toSite (rayX wReflex 1) ∈ Lint := by
-- proof
  apply StatMech.Onsager.InteriorRegion.launch_interior

/--
[wReflex_mem_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean)
-/
@[path]
private lemma wReflex_mem_boundary_eq :
-- imply
  wReflex ∈ (mkBoxData Lint Lint_finite).B := by
-- proof
  apply StatMech.Onsager.InteriorRegion.wReflex_mem_boundary

/--
[wReflex_isReflex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean)
-/
@[path]
private lemma wReflex_isReflex_eq :
-- imply
  cross (1, 0) (0, -1) = -1 ∧ (cross (1, 0) (1, 0) = 0 ∧ 0 < cross (0, -1) (1, 0)) := by
-- proof
  apply StatMech.Onsager.InteriorRegion.wReflex_isReflex

/--
[wReflex_quadrant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean)
-/
@[path]
private lemma wReflex_quadrant_eq :
-- imply
  (toSite (2, 1) ∈ Lint ∧ toSite (1, 2) ∈ Lint) ∧ (toSite (0, 1) ∉ Lint ∧ toSite (1, 0) ∉ Lint) := by
-- proof
  apply StatMech.Onsager.InteriorRegion.wReflex_quadrant

/--
[Lshape_interiorReaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean)
-/
@[path]
private lemma Lshape_interiorReaches_eq :
-- imply
  InteriorReaches (mkBoxData Lint Lint_finite) wReflex := by
-- proof
  apply StatMech.Onsager.InteriorRegion.Lshape_interiorReaches

/--
[Lshape_chord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean)
-/
@[path]
private lemma Lshape_chord_eq :
-- imply
  ∃ k : ℕ, 1 ≤ k ∧ rayX wReflex k ∈ (mkBoxData Lint Lint_finite).B ∧ (∀ j : ℕ, 1 ≤ j → j < k → rayX wReflex j ∉ (mkBoxData Lint Lint_finite).B) := by
-- proof
  apply StatMech.Onsager.InteriorRegion.Lshape_chord

/--
[interior_iff_odd_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean)
-/
@[path]
private lemma interior_iff_odd_crossing_eq
  {S : Set (Site 2)}
  {p : Pt}
  {N : ℕ}
-- given
  (hout : toSite (rayX p N) ∉ S) :
-- imply
  toSite p ∈ S ↔ ¬ Even (crossCount S (rayWalk p N)) := by
-- proof
  apply StatMech.Onsager.InteriorRegion.interior_iff_odd_crossing S p N hout


-- created on 2026-10-23
