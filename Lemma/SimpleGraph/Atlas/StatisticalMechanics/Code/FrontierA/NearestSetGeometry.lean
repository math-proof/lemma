import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.NearestSetGeometry.Part4
open Set StatMech StatMech.FrontierA


/--
[realizedL1Distances_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean)
-/
@[path]
private lemma realizedL1Distances_nonempty_eq
  {d : ℕ}
  {A B : Set (Site d)}
-- given
  (hA : A.Nonempty)
  (hB : B.Nonempty) :
-- imply
  (realizedL1Distances A B).Nonempty := by
-- proof
  apply StatMech.FrontierA.realizedL1Distances_nonempty hA hB

/--
[exists_pair_setL1Distance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean)
-/
@[path]
private lemma exists_pair_setL1Distance_eq
  {d : ℕ}
  {A B : Set (Site d)}
-- given
  (hA : A.Nonempty)
  (hB : B.Nonempty) :
-- imply
  ∃ x ∈ A, ∃ y ∈ B, l1dist d x y = setL1Distance A B := by
-- proof
  apply StatMech.FrontierA.exists_pair_setL1Distance hA hB

/--
[nearestSourceSet_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean)
-/
@[path]
private lemma nearestSourceSet_subset_eq
  {d : ℕ}
  {A B : Set (Site d)} :
-- imply
  nearestSourceSet A B ⊆ A := by
-- proof
  apply StatMech.FrontierA.nearestSourceSet_subset A B

/--
[nearestSourceSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean)
-/
@[path]
private lemma nearestSourceSet_nonempty_eq
  {d : ℕ}
  {A B : Set (Site d)}
-- given
  (hA : A.Nonempty)
  (hB : B.Nonempty) :
-- imply
  (nearestSourceSet A B).Nonempty := by
-- proof
  apply StatMech.FrontierA.nearestSourceSet_nonempty hA hB

/--
[mem_nearestSourceSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean)
-/
@[path]
private lemma mem_nearestSourceSet_iff_eq
  {d : ℕ}
  {A B : Set (Site d)}
  {x : Site d} :
-- imply
  x ∈ nearestSourceSet A B ↔ x ∈ A ∧ ∃ y ∈ B, ∀ x' ∈ A, ∀ y' ∈ B, l1dist d x y ≤ l1dist d x' y' := by
-- proof
  apply StatMech.FrontierA.mem_nearestSourceSet_iff

/--
[mem_nearestSourceFinset_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean)
-/
@[path]
private lemma mem_nearestSourceFinset_iff_eq
  {d : ℕ}
  {A B : Set (Site d)}
  {x : Site d}
-- given
  (hfin : (nearestSourceSet A B).Finite) :
-- imply
  x ∈ nearestSourceFinset A B ↔ x ∈ nearestSourceSet A B := by
-- proof
  apply StatMech.FrontierA.mem_nearestSourceFinset_iff hfin x

/--
[mem_nearestSourceSet_of_mem_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean)
-/
@[path]
private lemma mem_nearestSourceSet_of_mem_finset_eq
  {d : ℕ}
  {A B : Set (Site d)}
  {x : Site d}
-- given
  (hx : x ∈ nearestSourceFinset A B) :
-- imply
  x ∈ nearestSourceSet A B := by
-- proof
  apply StatMech.FrontierA.mem_nearestSourceSet_of_mem_finset hx

/--
[mem_nearestSourceFinset_iff_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean)
-/
@[path]
private lemma mem_nearestSourceFinset_iff_finite_eq
  {d : ℕ}
  {A B : Set (Site d)}
  {x : Site d} :
-- imply
  x ∈ nearestSourceFinset A B ↔ (nearestSourceSet A B).Finite ∧ x ∈ nearestSourceSet A B := by
-- proof
  apply StatMech.FrontierA.mem_nearestSourceFinset_iff_finite

/--
[nearestSourceFinset_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean)
-/
@[path]
private lemma nearestSourceFinset_card_eq
  {d : ℕ}
  {A B : Set (Site d)} :
-- imply
  (nearestSourceFinset A B).card = (nearestSourceSet A B).ncard := by
-- proof
  apply StatMech.FrontierA.nearestSourceFinset_card A B

/--
[nearestSourceFinset_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean)
-/
@[path]
private lemma nearestSourceFinset_nonempty_eq
  {d : ℕ}
  {A B : Set (Site d)}
-- given
  (hA : A.Nonempty)
  (hB : B.Nonempty)
  (hfin : (nearestSourceSet A B).Finite) :
-- imply
  (nearestSourceFinset A B).Nonempty := by
-- proof
  apply StatMech.FrontierA.nearestSourceFinset_nonempty hA hB hfin

/--
[l1dist_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean)
-/
@[path]
private lemma l1dist_translate_eq
  {d : ℕ}
  {a x y : Site d} :
-- imply
  l1dist d (a + x) (a + y) = l1dist d x y := by
-- proof
  apply StatMech.FrontierA.l1dist_translate a x y

/--
[realizedL1Distances_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean)
-/
@[path]
private lemma realizedL1Distances_translate_eq
  {d : ℕ}
  {a : Site d}
  {A B : Set (Site d)} :
-- imply
  realizedL1Distances (translateSiteSet a A) (translateSiteSet a B) = realizedL1Distances A B := by
-- proof
  apply StatMech.FrontierA.realizedL1Distances_translate a A B

/--
[setL1Distance_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean)
-/
@[path]
private lemma setL1Distance_translate_eq
  {d : ℕ}
  {a : Site d}
  {A B : Set (Site d)} :
-- imply
  setL1Distance (translateSiteSet a A) (translateSiteSet a B) = setL1Distance A B := by
-- proof
  apply StatMech.FrontierA.setL1Distance_translate a A B

/--
[nearestSourceSet_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean)
-/
@[path]
private lemma nearestSourceSet_translate_eq
  {d : ℕ}
  {a : Site d}
  {A B : Set (Site d)} :
-- imply
  nearestSourceSet (translateSiteSet a A) (translateSiteSet a B) = translateSiteSet a (nearestSourceSet A B) := by
-- proof
  apply StatMech.FrontierA.nearestSourceSet_translate a A B

/--
[nearestSourceFinset_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean)
-/
@[path]
private lemma nearestSourceFinset_translate_eq
  {d : ℕ}
  {a : Site d}
  {A B : Set (Site d)} :
-- imply
  nearestSourceFinset (translateSiteSet a A) (translateSiteSet a B) = (nearestSourceFinset A B).image (fun x => a + x) := by
-- proof
  apply StatMech.FrontierA.nearestSourceFinset_translate a A B


-- created on 2026-10-23
