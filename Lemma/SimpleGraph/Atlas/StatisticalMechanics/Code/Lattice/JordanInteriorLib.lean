import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[jil_floodFill_stepRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_floodFill_stepRight_eq
  {B : Set (Site 2)}
  {seed : Site 2}
  {x y : ℤ}
-- given
  (hz : (![x, y] : Site 2) ∈ ffc_floodFill B seed)
  (hzB : (![x, y] : Site 2) ∉ B)
  (hwB : (![x + 1, y] : Site 2) ∉ B) :
-- imply
  (![x + 1, y] : Site 2) ∈ ffc_floodFill B seed := by
-- proof
  apply StatMech.Lattice.jil_floodFill_stepRight B hz hzB hwB

/--
[jil_floodFill_run_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_floodFill_run_right_eq
  {B : Set (Site 2)}
  {seed : Site 2}
  {x₀ y : ℤ}
  {k : ℕ}
-- given
  (h0 : (![x₀, y] : Site 2) ∈ ffc_floodFill B seed)
  (hoff : ∀ t : ℕ, t ≤ k → (![x₀ + (t : ℤ), y] : Site 2) ∉ B) :
-- imply
  (![x₀ + (k : ℤ), y] : Site 2) ∈ ffc_floodFill B seed := by
-- proof
  apply StatMech.Lattice.jil_floodFill_run_right B k h0 hoff

/--
[jil_localConstancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_localConstancy_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ Vc.support)
  (hv : v ∉ Vc.support) :
-- imply
  (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc)) := by
-- proof
  apply StatMech.Lattice.jil_localConstancy Vc hadj hu hv

/--
[jil_floodFill_sameParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_floodFill_sameParity_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {z : Site 2}
-- given
  (hseed : seed ∉ Vc.support)
  (hz : z ∈ ffc_floodFill {p | p ∈ Vc.support} seed) :
-- imply
  (Even (jec_rayCount seed Vc) ↔ Even (jec_rayCount z Vc)) := by
-- proof
  apply StatMech.Lattice.jil_floodFill_sameParity Vc hseed hz

/--
[jil_floodFill_subset_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_floodFill_subset_leftRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseed : seed ∉ Vc.support)
  (hseedIn : seed ∈ jec_leftRegion Vc) :
-- imply
  ffc_floodFill {p | p ∈ Vc.support} seed ⊆ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.jil_floodFill_subset_leftRegion Vc hseed hseedIn

/--
[jil_floodFill_subset_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_floodFill_subset_exterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseed : seed ∉ Vc.support)
  (hseedOut : seed ∉ jec_leftRegion Vc) :
-- imply
  ffc_floodFill {p | p ∈ Vc.support} seed ⊆ (jec_leftRegion Vc)ᶜ := by
-- proof
  apply StatMech.Lattice.jil_floodFill_subset_exterior Vc hseed hseedOut

/--
[jil_hsegment_mem_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_hsegment_mem_floodFill_eq
  {B : Set (Site 2)}
  {lo hi y x : ℤ}
-- given
  (hxlo : lo ≤ x)
  (hxhi : x ≤ hi)
  (hoff : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, y] : Site 2) ∉ B) :
-- imply
  (![x, y] : Site 2) ∈ ffc_floodFill B (![lo, y] : Site 2) := by
-- proof
  apply StatMech.Lattice.jil_hsegment_mem_floodFill B hxlo hxhi hoff

/--
[jil_hsegment_reachable_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_hsegment_reachable_offSupport_eq
  {B : Set (Site 2)}
  {lo hi y x₁ x₂ : ℤ}
-- given
  (hloB : (![lo, y] : Site 2) ∉ B)
  (hx₁lo : lo ≤ x₁)
  (hx₁hi : x₁ ≤ hi)
  (hx₂lo : lo ≤ x₂)
  (hx₂hi : x₂ ≤ hi)
  (hoff : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, y] : Site 2) ∉ B) :
-- imply
  ∃ p : (hypercubicLattice 2).Walk (![x₁, y] : Site 2) ![x₂, y], ∀ z ∈ p.support, z ∉ B := by
-- proof
  apply StatMech.Lattice.jil_hsegment_reachable_offSupport B hloB hx₁lo hx₁hi hx₂lo hx₂hi hoff

/--
[jil_hsegment_sameParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_hsegment_sameParity_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {lo hi y x : ℤ}
-- given
  (hloB : (![lo, y] : Site 2) ∉ Vc.support)
  (hxlo : lo ≤ x)
  (hxhi : x ≤ hi)
  (hoff : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, y] : Site 2) ∉ Vc.support) :
-- imply
  (Even (jec_rayCount (![lo, y] : Site 2) Vc) ↔ Even (jec_rayCount (![x, y] : Site 2) Vc)) := by
-- proof
  apply StatMech.Lattice.jil_hsegment_sameParity Vc hloB hxlo hxhi hoff

/--
[jil_hsegment_subset_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_hsegment_subset_leftRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {lo hi y x₀ x : ℤ}
-- given
  (hx₀lo : lo ≤ x₀)
  (hx₀hi : x₀ ≤ hi)
  (hxlo : lo ≤ x)
  (hxhi : x ≤ hi)
  (hoff : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, y] : Site 2) ∉ Vc.support)
  (hin : (![x₀, y] : Site 2) ∈ jec_leftRegion Vc) :
-- imply
  (![x, y] : Site 2) ∈ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.jil_hsegment_subset_leftRegion Vc hx₀lo hx₀hi hxlo hxhi hoff hin

/--
[jil_mem_offSupportInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_mem_offSupportInterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2} :
-- imply
  z ∈ jil_offSupportInterior Vc ↔ z ∉ Vc.support ∧ z ∈ jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.jil_mem_offSupportInterior Vc z

/--
[jil_floodFill_subset_offSupportInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_floodFill_subset_offSupportInterior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseed : seed ∉ Vc.support)
  (hseedIn : seed ∈ jec_leftRegion Vc) :
-- imply
  ffc_floodFill {p | p ∈ Vc.support} seed ⊆ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.jil_floodFill_subset_offSupportInterior Vc hseed hseedIn

/--
[jil_offSupportInterior_subset_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_offSupportInterior_subset_floodFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hlink : jil_RowLinked Vc seed) :
-- imply
  jil_offSupportInterior Vc ⊆ ffc_floodFill {p | p ∈ Vc.support} seed := by
-- proof
  apply StatMech.Lattice.jil_offSupportInterior_subset_floodFill Vc hlink

/--
[jil_offSupportInterior_eq_floodFill](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_offSupportInterior_eq_floodFill_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseed : seed ∉ Vc.support)
  (hseedIn : seed ∈ jec_leftRegion Vc)
  (hlink : jil_RowLinked Vc seed) :
-- imply
  jil_offSupportInterior Vc = ffc_floodFill {p | p ∈ Vc.support} seed := by
-- proof
  apply StatMech.Lattice.jil_offSupportInterior_eq_floodFill Vc hseed hseedIn hlink

/--
[jil_stepGraph_walk_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_stepGraph_walk_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : jil_offSupportInterior Vc}
  {w : (jil_interiorStepGraph Vc).Walk x y} :
-- imply
  ∃ p : (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2), ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.jil_stepGraph_walk_offSupport Vc w

/--
[jil_rowLinked_of_stepReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_rowLinked_of_stepReachable_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hstep : ∀ z : jil_offSupportInterior Vc, (jil_interiorStepGraph Vc).Reachable z ⟨seed, hseedI⟩) :
-- imply
  jil_RowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.jil_rowLinked_of_stepReachable Vc hseedI hstep

/--
[jil_stepGraph_horizontal_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_stepGraph_horizontal_adj_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : ℤ}
-- given
  (hu : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hv : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc) :
-- imply
  (jil_interiorStepGraph Vc).Adj ⟨![x, y], hu⟩ ⟨![x + 1, y], hv⟩ := by
-- proof
  apply StatMech.Lattice.jil_stepGraph_horizontal_adj Vc hu hv

/--
[jil_stepGraph_vertical_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean)
-/
@[path]
private lemma jil_stepGraph_vertical_adj_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : ℤ}
-- given
  (hu : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hv : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc) :
-- imply
  (jil_interiorStepGraph Vc).Adj ⟨![x, y], hu⟩ ⟨![x, y + 1], hv⟩ := by
-- proof
  apply StatMech.Lattice.jil_stepGraph_vertical_adj Vc hu hv


-- created on 2026-10-23
