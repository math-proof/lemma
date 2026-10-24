import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.gh7resum
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gh7_sumA_is_per_superposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh7resum.lean)
-/
@[path]
private lemma gh7_sumA_is_per_superposition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {V₁ V₂ : Finset W}
  {u : W} :
-- imply
  gc85b_pcount ends m V₁ V₂ = ∑ A ∈ m.powerset, gh4_compMass ends m V₁ V₂ u A := by
-- proof
  apply StatMech.Walls.gh7_sumA_is_per_superposition G ends m V₁ V₂ u

/--
[gh7_threeGapCount_component_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh7resum.lean)
-/
@[path]
private lemma gh7_threeGapCount_component_decomp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  gc85b_threeGapCount ends m o x y g = ∑ A ∈ m.powerset, ((gh4_compMass ends m ∅ ∅ o A : ℤ) - (gh4_compMass ends m ∅ {o, g} o A : ℤ) - (gh4_compMass ends m ∅ {o, x} o A : ℤ) - (gh4_compMass ends m ∅ {o, y} o A : ℤ) + 2 * (gh4_compMass ends m {o, g} {x, g} o A : ℤ)) := by
-- proof
  apply StatMech.Walls.gh7_threeGapCount_component_decomp G ends m o x y g

/--
[gh7_resummation_assembly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh7resum.lean)
-/
@[path]
private lemma gh7_resummation_assembly_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hsign : ∀ m : ↥(withGhost G).edgeFinset → ℕ, gc15_threeGap G β h o x y m ≤ 0) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gh7_resummation_assembly G β h o x y hox hoy hxy hsign

/--
[gh7_ghs_of_perSuperposition_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh7resum.lean)
-/
@[path]
private lemma gh7_ghs_of_perSuperposition_count_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hbij : ∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gc85b_ThreeCurrentBijection (endsM (withGhost G) m) univ (some o) (some x) (some y) none)
  (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gh7_ghs_of_perSuperposition_count G β h hβ hh o x y hox hoy hxy hbij hsupp

/--
[gh7_perSuperposition_drop_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh7resum.lean)
-/
@[path]
private lemma gh7_perSuperposition_drop_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {V₁ V₂ : Finset W}
  {u : W}
  {wgt diff : Finset ι → ℝ}
-- given
  (hwgt : ∀ A, 0 ≤ wgt A)
  (hdiff : ∀ A, 0 ≤ diff A) :
-- imply
  0 ≤ ∑ A ∈ m.powerset, (gh4_compMass ends m V₁ V₂ u A : ℝ) * wgt A * diff A := by
-- proof
  apply StatMech.Walls.gh7_perSuperposition_drop_nonneg G ends m V₁ V₂ u wgt diff hwgt hdiff

/--
[gh7_perSuperposition_count_nonpos_of_eq22](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh7resum.lean)
-/
@[path]
private lemma gh7_perSuperposition_count_nonpos_of_eq22_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (heq22 : gh7_perSuperposition_eq22 ends m o x y g) :
-- imply
  (gc85b_threeGapCount ends m o x y g : ℝ) ≤ 0 := by
-- proof
  apply StatMech.Walls.gh7_perSuperposition_count_nonpos_of_eq22 G ends m o x y g heq22

/--
[gh7_ghs_of_perSuperposition_eq22](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh7resum.lean)
-/
@[path]
private lemma gh7_ghs_of_perSuperposition_eq22_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (heq22 : ∀ m : ↥(withGhost G).edgeFinset → ℕ, sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V)) → gh7_perSuperposition_eq22 (endsM (withGhost G) m) univ (some o) (some x) (some y) none)
  (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gh7_ghs_of_perSuperposition_eq22 G β h hβ hh o x y hox hoy hxy heq22 hsupp

/--
[gh7_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh7resum.lean)
-/
@[path]
private lemma gh7_status_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gh7_status G


-- created on 2026-10-23
