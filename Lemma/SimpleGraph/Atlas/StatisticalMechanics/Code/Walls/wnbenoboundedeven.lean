import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.wnbenoboundedeven
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[wnbe_component_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_component_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed z : Site 2}
-- given
  (hseed : seed ∉ Vc.support)
  (hz : z ∈ offSupportComponent Vc seed) :
-- imply
  z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.wnbe_component_offSupport Vc hseed hz

/--
[wnbe_component_boundary_onSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_component_boundary_onSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed z w : Site 2}
-- given
  (hseed : seed ∉ Vc.support)
  (hz : z ∈ offSupportComponent Vc seed)
  (hadj : (hypercubicLattice 2).Adj z w)
  (hw : w ∉ offSupportComponent Vc seed) :
-- imply
  w ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.wnbe_component_boundary_onSupport Vc hseed hz hadj hw

/--
[wnbe_neighbour_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_neighbour_dichotomy_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed z w : Site 2}
-- given
  (hseed : seed ∉ Vc.support)
  (hz : z ∈ offSupportComponent Vc seed)
  (hadj : (hypercubicLattice 2).Adj z w) :
-- imply
  w ∈ offSupportComponent Vc seed ∨ w ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.wnbe_neighbour_dichotomy Vc hseed hz hadj

/--
[wnbe_adjacent_same_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_adjacent_same_component_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed z w : Site 2}
-- given
  (hseed : seed ∉ Vc.support)
  (hz : z ∈ offSupportComponent Vc seed)
  (hadj : (hypercubicLattice 2).Adj z w)
  (hwoff : w ∉ Vc.support) :
-- imply
  w ∈ offSupportComponent Vc seed := by
-- proof
  apply StatMech.Lattice.wnbe_adjacent_same_component Vc hseed hz hadj hwoff

/--
[wnbe_distinct_components_support_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_distinct_components_support_separated_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {s₁ s₂ z w : Site 2}
-- given
  (h₁ : s₁ ∉ Vc.support)
  (h₂ : s₂ ∉ Vc.support)
  (hz : z ∈ offSupportComponent Vc s₁)
  (hw : w ∈ offSupportComponent Vc s₂)
  (hadj : (hypercubicLattice 2).Adj z w)
  (hwoff : w ∉ Vc.support)
  (hne : offSupportComponent Vc s₁ ≠ offSupportComponent Vc s₂) :
-- imply
  False := by
-- proof
  apply StatMech.Lattice.wnbe_distinct_components_support_separated Vc h₁ h₂ hz hw hadj hwoff hne

/--
[wnbe_rayEdge_cells](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_rayEdge_cells_eq
  {a : Site 2}
  {z x y : Site 2}
-- given
  (h : jec_rayEdge z s(x, y)) :
-- imply
  x 0 = y 0 ∧ x 0 ≤ z 0 - 1 ∧ ((x 1 = z 1 - 1 ∧ y 1 = z 1) ∨ (x 1 = z 1 ∧ y 1 = z 1 - 1)) := by
-- proof
  apply StatMech.Lattice.wnbe_rayEdge_cells h

/--
[wnbe_rayCount_zero_of_noLeftSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_rayCount_zero_of_noLeftSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hno : ∀ c : ℤ, c < z 0 → (![c, z 1] : Site 2) ∉ Vc.support ∧ (![c, z 1 - 1] : Site 2) ∉ Vc.support) :
-- imply
  jec_rayCount z Vc = 0 := by
-- proof
  apply StatMech.Lattice.wnbe_rayCount_zero_of_noLeftSupport Vc hno

/--
[wnbe_notInterior_of_noLeftSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_notInterior_of_noLeftSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hno : ∀ c : ℤ, c < z 0 → (![c, z 1] : Site 2) ∉ Vc.support ∧ (![c, z 1 - 1] : Site 2) ∉ Vc.support) :
-- imply
  z ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.wnbe_notInterior_of_noLeftSupport Vc hno

/--
[wnbe_interior_hasLeftSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_interior_hasLeftSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hz : z ∈ jec_leftRegion Vc) :
-- imply
  ∃ c : ℤ, c < z 0 ∧ ((![c, z 1] : Site 2) ∈ Vc.support ∨ (![c, z 1 - 1] : Site 2) ∈ Vc.support) := by
-- proof
  apply StatMech.Lattice.wnbe_interior_hasLeftSupport Vc hz

/--
[wnbe_horizRun_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_horizRun_reachable_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {y x0 x1 : ℤ}
-- given
  (hoff : ∀ t : ℤ, t ∈ Set.uIcc x0 x1 → (![t, y] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable (![x0, y] : Site 2) ![x1, y] := by
-- proof
  apply StatMech.Lattice.wnbe_horizRun_reachable Vc y x0 x1 hoff

/--
[wnbe_vertRun_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_vertRun_reachable_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y0 y1 : ℤ}
-- given
  (hoff : ∀ t : ℤ, t ∈ Set.uIcc y0 y1 → (![x, t] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable (![x, y0] : Site 2) ![x, y1] := by
-- proof
  apply StatMech.Lattice.wnbe_vertRun_reachable Vc x y0 y1 hoff

/--
[wnbe_horizRun_sameComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_horizRun_sameComponent_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {y x0 x1 : ℤ}
-- given
  (hoff : ∀ t : ℤ, t ∈ Set.uIcc x0 x1 → (![t, y] : Site 2) ∉ Vc.support)
  (hz : (![x0, y] : Site 2) ∈ offSupportComponent Vc seed) :
-- imply
  (![x1, y] : Site 2) ∈ offSupportComponent Vc seed := by
-- proof
  apply StatMech.Lattice.wnbe_horizRun_sameComponent Vc hoff hz

/--
[wnbe_horizRun_sameLeftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_horizRun_sameLeftRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {y x0 x1 : ℤ}
-- given
  (hoff : ∀ t : ℤ, t ∈ Set.uIcc x0 x1 → (![t, y] : Site 2) ∉ Vc.support) :
-- imply
  ((![x0, y] : Site 2) ∈ jec_leftRegion Vc) ↔ ((![x1, y] : Site 2) ∈ jec_leftRegion Vc) := by
-- proof
  apply StatMech.Lattice.wnbe_horizRun_sameLeftRegion Vc hoff

/--
[wnbe_vertRun_sameLeftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_vertRun_sameLeftRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y0 y1 : ℤ}
-- given
  (hoff : ∀ t : ℤ, t ∈ Set.uIcc y0 y1 → (![x, t] : Site 2) ∉ Vc.support) :
-- imply
  ((![x, y0] : Site 2) ∈ jec_leftRegion Vc) ↔ ((![x, y1] : Site 2) ∈ jec_leftRegion Vc) := by
-- proof
  apply StatMech.Lattice.wnbe_vertRun_sameLeftRegion Vc hoff

/--
[wnbe_LPath_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_LPath_reachable_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x0 y0 x1 y1 : ℤ}
-- given
  (hhor : ∀ t : ℤ, t ∈ Set.uIcc x0 x1 → (![t, y0] : Site 2) ∉ Vc.support)
  (hver : ∀ t : ℤ, t ∈ Set.uIcc y0 y1 → (![x1, t] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable (![x0, y0] : Site 2) ![x1, y1] := by
-- proof
  apply StatMech.Lattice.wnbe_LPath_reachable Vc x0 y0 x1 y1 hhor hver

/--
[wnbe_LPath_sameComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_LPath_sameComponent_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {x0 y0 x1 y1 : ℤ}
-- given
  (hhor : ∀ t : ℤ, t ∈ Set.uIcc x0 x1 → (![t, y0] : Site 2) ∉ Vc.support)
  (hver : ∀ t : ℤ, t ∈ Set.uIcc y0 y1 → (![x1, t] : Site 2) ∉ Vc.support)
  (hz : (![x0, y0] : Site 2) ∈ offSupportComponent Vc seed) :
-- imply
  (![x1, y1] : Site 2) ∈ offSupportComponent Vc seed := by
-- proof
  apply StatMech.Lattice.wnbe_LPath_sameComponent Vc hhor hver hz

/--
[wnbe_clearRight_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_clearRight_reachesExterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hclear : ∀ t : ℤ, t ∈ Set.uIcc (z 0) ((R : ℤ) + 1) → (![t, z 1] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable z (![(R : ℤ) + 1, z 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.wnbe_clearRight_reachesExterior Vc R hclear

/--
[wnbe_escapable_component_meets_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_escapable_component_meets_exterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {seed z : Site 2}
-- given
  (hclear : ∀ t : ℤ, t ∈ Set.uIcc (z 0) ((R : ℤ) + 1) → (![t, z 1] : Site 2) ∉ Vc.support)
  (hz : z ∈ offSupportComponent Vc seed) :
-- imply
  (![(R : ℤ) + 1, z 1] : Site 2) ∈ offSupportComponent Vc seed := by
-- proof
  apply StatMech.Lattice.wnbe_escapable_component_meets_exterior Vc R hclear hz

/--
[wnbe_clearLeft_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_clearLeft_reachesExterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hclear : ∀ t : ℤ, t ∈ Set.uIcc (z 0) (-(R : ℤ) - 1) → (![t, z 1] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable z (![-(R : ℤ) - 1, z 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.wnbe_clearLeft_reachesExterior Vc R hclear

/--
[wnbe_clearUp_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_clearUp_reachesExterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hclear : ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable z (![z 0, (R : ℤ) + 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.wnbe_clearUp_reachesExterior Vc R hclear

/--
[wnbe_clearDown_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnbenoboundedeven.lean)
-/
@[path]
private lemma wnbe_clearDown_reachesExterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hclear : ∀ t : ℤ, t ∈ Set.uIcc (z 1) (-(R : ℤ) - 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
-- imply
  (offSupport Vc).Reachable z (![z 0, -(R : ℤ) - 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.wnbe_clearDown_reachesExterior Vc R hclear


-- created on 2026-10-23
