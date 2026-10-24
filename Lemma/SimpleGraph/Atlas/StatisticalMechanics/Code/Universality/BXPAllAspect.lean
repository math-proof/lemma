import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.BXPAllAspect
open Set MeasureTheory SimpleGraph StatMech StatMech.Universality


/--
[bxa_adj_coord_diff_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAllAspect.lean)
-/
@[path]
private lemma bxa_adj_coord_diff_le_eq
  {d : ℕ}
  {x y : Site d}
  {i : Fin d}
-- given
  (h : (hypercubicLattice d).Adj x y) :
-- imply
  (x i - y i).natAbs ≤ 1 := by
-- proof
  apply StatMech.Universality.bxa_adj_coord_diff_le h i

/--
[bxa_walk_first_hit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAllAspect.lean)
-/
@[path]
private lemma bxa_walk_first_hit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {p : (openSubgraph 2 ω).Walk x y}
  {i : Fin 2}
  {t : ℤ}
-- given
  (hx : x i < t)
  (hy : t ≤ y i) :
-- imply
  ∃ j ≤ p.length, (p.getVert j) i = t ∧ ∀ m < j, (p.getVert m) i < t := by
-- proof
  apply StatMech.Universality.bxa_walk_first_hit p i t hx hy

/--
[bxa_connectedWithin_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAllAspect.lean)
-/
@[path]
private lemma bxa_connectedWithin_restrict_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {S T : Set (Site 2)}
  {x y : Site 2}
  {i : Fin 2}
  {t : ℤ}
-- given
  (hxS : x ∈ S)
  (hyS : y ∈ S)
  (h : ConnectedWithin 2 ω S ⟨x, hxS⟩ ⟨y, hyS⟩)
  (hx : x i < t)
  (hy : t ≤ y i)
  (hslab : ∀ z ∈ S, z i ≤ t → z ∈ T) :
-- imply
  ∃ (u : Site 2) (_ : u ∈ S), u i = t ∧ ∃ (huT : u ∈ T) (hxT : x ∈ T), ConnectedWithin 2 ω T ⟨x, hxT⟩ ⟨u, huT⟩ := by
-- proof
  apply StatMech.Universality.bxa_connectedWithin_restrict hxS hyS h i t hx hy hslab

/--
[bxa_horizontalCrossing_mono_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAllAspect.lean)
-/
@[path]
private lemma bxa_horizontalCrossing_mono_width_eq
  {a a' b : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (ha : 0 < a)
  (haa' : a ≤ a')
  (h : HorizontalCrossing ω 0 a' 0 b) :
-- imply
  HorizontalCrossing ω 0 a 0 b := by
-- proof
  apply StatMech.Universality.bxa_horizontalCrossing_mono_width ha haa' h

/--
[bxa_verticalCrossing_mono_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAllAspect.lean)
-/
@[path]
private lemma bxa_verticalCrossing_mono_height_eq
  {a d d' : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hd : 0 < d)
  (hdd' : d ≤ d')
  (h : VerticalCrossing ω 0 a 0 d') :
-- imply
  VerticalCrossing ω 0 a 0 d := by
-- proof
  apply StatMech.Universality.bxa_verticalCrossing_mono_height hd hdd' h

/--
[bxa_horizontalCrossingEvent_subset_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAllAspect.lean)
-/
@[path]
private lemma bxa_horizontalCrossingEvent_subset_width_eq
  {a a' b : ℤ}
-- given
  (ha : 0 < a)
  (haa' : a ≤ a') :
-- imply
  horizontalCrossingEvent 0 a' 0 b ⊆ horizontalCrossingEvent 0 a 0 b := by
-- proof
  apply StatMech.Universality.bxa_horizontalCrossingEvent_subset_width ha haa'

/--
[bxa_verticalCrossingEvent_subset_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAllAspect.lean)
-/
@[path]
private lemma bxa_verticalCrossingEvent_subset_height_eq
  {a d d' : ℤ}
-- given
  (hd : 0 < d)
  (hdd' : d ≤ d') :
-- imply
  verticalCrossingEvent 0 a 0 d' ⊆ verticalCrossingEvent 0 a 0 d := by
-- proof
  apply StatMech.Universality.bxa_verticalCrossingEvent_subset_height hd hdd'

/--
[bxa_horizontalCrossing_real_mono_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAllAspect.lean)
-/
@[path]
private lemma bxa_horizontalCrossing_real_mono_width_eq
  {a a' b : ℤ}
-- given
  (ha : 0 < a)
  (haa' : a ≤ a') :
-- imply
  rba_selfDualMeasure.real (horizontalCrossingEvent 0 a' 0 b) ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 a 0 b) := by
-- proof
  apply StatMech.Universality.bxa_horizontalCrossing_real_mono_width ha haa'

/--
[bxa_verticalCrossing_real_mono_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAllAspect.lean)
-/
@[path]
private lemma bxa_verticalCrossing_real_mono_height_eq
  {a d d' : ℤ}
-- given
  (hd : 0 < d)
  (hdd' : d ≤ d') :
-- imply
  rba_selfDualMeasure.real (verticalCrossingEvent 0 a 0 d') ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 a 0 d) := by
-- proof
  apply StatMech.Universality.bxa_verticalCrossing_real_mono_height hd hdd'

/--
[bxa_floor_le_natMul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAllAspect.lean)
-/
@[path]
private lemma bxa_floor_le_natMul_eq
  {ρ : ℝ}
  {k0 : ℕ}
  {n : ℕ}
-- given
  (hρk0 : ρ ≤ (k0 : ℝ)) :
-- imply
  ⌊ρ * (n : ℝ)⌋ ≤ (k0 : ℤ) * (n : ℤ) := by
-- proof
  apply StatMech.Universality.bxa_floor_le_natMul hρk0 n

/--
[bxa_zero_lt_floor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAllAspect.lean)
-/
@[path]
private lemma bxa_zero_lt_floor_eq
  {ρ : ℝ}
  {n : ℕ}
-- given
  (hρ : 1 < ρ)
  (hn : 1 ≤ n) :
-- imply
  (0 : ℤ) < ⌊ρ * (n : ℝ)⌋ := by
-- proof
  apply StatMech.Universality.bxa_zero_lt_floor hρ hn

/--
[bxa_boxCrossingProperty_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAllAspect.lean)
-/
@[path]
private lemma bxa_boxCrossingProperty_all_eq
  {β γ : ℝ}
-- given
  (hpa : PositivelyAssociated rba_selfDualMeasure)
  (hβ : 0 < β)
  (hγ : 0 < γ)
  (hmeas2box : ∀ n : ℤ, 0 < n → MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
  (hmeasband : ∀ n : ℤ, 0 < n → MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (horizontalCrossingEvent 0 a 0 b))
  (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (verticalCrossingEvent 0 a 0 b))
  (hseed : ∀ n : ℤ, 0 < n → β ≤ rai_cross rba_selfDualMeasure n 1)
  (h2box : ∀ n : ℤ, 0 < n → γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
  (hband : ∀ n : ℤ, 0 < n → (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n))
  (hrefl : ∀ (k0 : ℕ), 2 ≤ k0 → ∀ n : ℤ, 0 < n → rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n)) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n)) :
-- imply
  ∀ ρ : ℝ, 1 < ρ → BoxCrossingProperty rba_selfDualMeasure ρ := by
-- proof
  apply StatMech.Universality.bxa_boxCrossingProperty_all hpa hβ hγ hmeas2box hmeasband hmeasGenH hmeasGenV hseed h2box hband hrefl


-- created on 2026-10-23
