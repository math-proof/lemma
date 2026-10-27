import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gharesumassembly
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gha_poly_resum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gharesumassembly.lean)
-/
@[path]
private lemma gha_poly_resum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y) :
-- imply
  (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y = ∑' m : ↥(withGhost G).edgeFinset → ℕ, gc15_threeGap G β h o x y m := by
-- proof
  apply StatMech.Walls.gha_poly_resum G β h o x y hox hoy hxy

/--
[gha_poly_resum_check](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gharesumassembly.lean)
-/
@[path]
private lemma gha_poly_resum_check_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {m : ↥(withGhost G).edgeFinset → ℕ}
-- given
  (β h : ℝ)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m) = ({some o, some x, some y, none} : Finset (Option V))) :
-- imply
  gc15_threeGap G β h o x y m = (gc85b_threeGapCount (endsM (withGhost G) m) univ (some o) (some x) (some y) none : ℝ) * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) := by
-- proof
  apply StatMech.Walls.gha_poly_resum_check G β h o x y hox hoy hxy m hm

/--
[gha_perm_rearrange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gharesumassembly.lean)
-/
@[path]
private lemma gha_perm_rearrange_eq
  [Fintype V]
  [DecidableEq V]
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
  apply StatMech.Walls.gha_perm_rearrange ends m o x y g heq22

/--
[gha_perm_sign_iff_bijection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gharesumassembly.lean)
-/
@[path]
private lemma gha_perm_sign_iff_bijection_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  gc85b_threeGapCount ends m o x y g ≤ 0 ↔ gc85b_ThreeCurrentBijection ends m o x y g := by
-- proof
  apply StatMech.Walls.gha_perm_sign_iff_bijection ends m o x y g

/--
[gha_weighted_eq22_of_ghs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gharesumassembly.lean)
-/
@[path]
private lemma gha_weighted_eq22_of_ghs_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {u u' : W}
-- given
  (β h : ℝ)
  (hghs : eg_ursell3 G β h o x y ≤ 0) :
-- imply
  gh8_weighted_eq22 G β h o x y ends m u u' := by
-- proof
  apply StatMech.Walls.gha_weighted_eq22_of_ghs G β h o x y ends m u u' hghs

/--
[gha_ghs_of_weighted_eq22](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gharesumassembly.lean)
-/
@[path]
private lemma gha_ghs_of_weighted_eq22_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {u u' : W}
-- given
  (β h : ℝ)
  (heq22 : gh8_weighted_eq22 G β h o x y ends m u u') :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gha_ghs_of_weighted_eq22 G β h o x y ends m u u' heq22

/--
[gha_weighted_eq22_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gharesumassembly.lean)
-/
@[path]
private lemma gha_weighted_eq22_iff_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {u u' : W}
-- given
  (β h : ℝ) :
-- imply
  gh8_weighted_eq22 G β h o x y ends m u u' ↔ eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gha_weighted_eq22_iff G β h o x y ends m u u'

/--
[gha_ghs_of_bijection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gharesumassembly.lean)
-/
@[path]
private lemma gha_ghs_of_bijection_eq
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
  apply StatMech.Walls.gha_ghs_of_bijection G β h hβ hh o x y hox hoy hxy hbij hsupp

/--
[gha_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gharesumassembly.lean)
-/
@[path]
private lemma gha_status_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gha_status


-- created on 2026-10-23
