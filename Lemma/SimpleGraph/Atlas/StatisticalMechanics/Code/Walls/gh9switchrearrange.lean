import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gh9switchrearrange.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gh9_pcount_regroup_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh9switchrearrange.lean)
-/
@[path]
private lemma gh9_pcount_regroup_real_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {V₁ V₂ : Finset W}
  {u : W} :
-- imply
  (gc85b_pcount ends m V₁ V₂ : ℝ) = ∑ A ∈ m.powerset, (gh4_compMass ends m V₁ V₂ u A : ℝ) := by
-- proof
  apply StatMech.Walls.gh9_pcount_regroup_real ends m V₁ V₂ u

/--
[gh9_lemma2_reroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh9switchrearrange.lean)
-/
@[path]
private lemma gh9_lemma2_reroute_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {A B : Finset W}
  {u v : W}
  {P : Finset ι}
-- given
  (huv : u ≠ v)
  (hPm : P ⊆ m)
  (hPsrc : sources ends P = {u, v}) :
-- imply
  #((m.powerset ×ˢ m.powerset).filter (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B ∆ {u, v})) = #((m.powerset ×ˢ m.powerset).filter (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B)) := by
-- proof
  apply StatMech.Walls.gh9_lemma2_reroute ends m A B huv P hPm hPsrc

/--
[gh9_flux_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh9switchrearrange.lean)
-/
@[path]
private lemma gh9_flux_dichotomy_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {ends : ι → Sym2 W}
  {R : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag)
  (hsrc : sources ends R = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g) :
-- imply
  Odd (#((({x, y, g} : Finset W)).filter (fun w => connK ends R o w))) := by
-- proof
  apply StatMech.Walls.gh9_flux_dichotomy ends R hnd hsrc hox hoy hog

/--
[gh9_ursell3_currentSum_poly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh9switchrearrange.lean)
-/
@[path]
private lemma gh9_ursell3_currentSum_poly_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
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
  (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y = (gc15_Z0 G β h) ^ 2 * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) - (gc15_Z0 G β h) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o} : Finset V).map someEmb)) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({x, y} : Finset V).map someEmb) - (gc15_Z0 G β h) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({o, x} : Finset V).map someEmb) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({y} : Finset V).map someEmb)) - (gc15_Z0 G β h) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (({o, y} : Finset V).map someEmb) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({x} : Finset V).map someEmb)) + 2 * (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({o} : Finset V).map someEmb)) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({x} : Finset V).map someEmb)) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (insert (none : Option V) (({y} : Finset V).map someEmb))) := by
-- proof
  apply StatMech.Walls.gh9_ursell3_currentSum_poly G β h o x y hox hoy hxy

/--
[gh9_weighted_eq22_of_perSuperposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh9switchrearrange.lean)
-/
@[path]
private lemma gh9_weighted_eq22_of_perSuperposition_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {u u' : W}
-- given
  (β h : ℝ)
  (hps : gh9_perSuperposition_weighted_eq22 G β h o x y ends m u u') :
-- imply
  gh8_weighted_eq22 G β h o x y ends m u u' := by
-- proof
  apply StatMech.Walls.gh9_weighted_eq22_of_perSuperposition G β h o x y ends m u u' hps

/--
[gh9_perSuperposition_iff_eq22](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh9switchrearrange.lean)
-/
@[path]
private lemma gh9_perSuperposition_iff_eq22_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {u u' : W}
-- given
  (β h : ℝ) :
-- imply
  gh9_perSuperposition_weighted_eq22 G β h o x y ends m u u' ↔ gh8_weighted_eq22 G β h o x y ends m u u' := by
-- proof
  apply StatMech.Walls.gh9_perSuperposition_iff_eq22 G β h o x y ends m u u'

/--
[gh9_ghs_of_perSuperposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh9switchrearrange.lean)
-/
@[path]
private lemma gh9_ghs_of_perSuperposition_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {u u' : W}
-- given
  (β h : ℝ)
  (hps : gh9_perSuperposition_weighted_eq22 G β h o x y ends m u u') :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gh9_ghs_of_perSuperposition G β h o x y ends m u u' hps

/--
[gh9_smallmodel_check](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh9switchrearrange.lean)
-/
@[path]
private lemma gh9_smallmodel_check_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {u u' : W}
-- given
  (β h : ℝ)
  (hzero : eg_ursell3 G β h o x y = 0) :
-- imply
  eg_ursell3 G β h o x y ≤ 0 := by
-- proof
  apply StatMech.Walls.gh9_smallmodel_check G β h o x y ends m u u' hzero

/--
[gh9_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh9switchrearrange.lean)
-/
@[path]
private lemma gh9_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.gh9_status


-- created on 2026-10-23
