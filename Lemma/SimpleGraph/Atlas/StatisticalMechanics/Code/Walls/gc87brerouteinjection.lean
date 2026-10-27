import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc87brerouteinjection.Part3
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc87b_connK_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean)
-/
@[path]
private lemma gc87b_connK_mono_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {K R : Finset ι}
  {a b : W}
-- given
  (hKR : K ⊆ R)
  (h : connK ends K a b) :
-- imply
  connK ends R a b := by
-- proof
  apply StatMech.Walls.gc87b_connK_mono ends hKR h

/--
[gc87b_ncount_xg_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean)
-/
@[path]
private lemma gc87b_ncount_xg_eq_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {R : Finset ι}
  {x g : W}
-- given
  (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag)
  (hxg : x ≠ g) :
-- imply
  gc86b_ncount ends R {x, g} = if connK ends R x g then gc86b_ncount ends R ∅ else 0 := by
-- proof
  apply StatMech.Walls.gc87b_ncount_xg_eq ends R hnd hxg

/--
[gc87b_cogxg_fiber_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean)
-/
@[path]
private lemma gc87b_cogxg_fiber_conn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hxg : x ≠ g) :
-- imply
  gc85b_pcount ends m {o, g} {x, g} = ∑ K₁ ∈ (m.powerset.filter (fun K => sources ends K = {o, g})).filter (fun K₁ => connK ends (m \ K₁) x g), gc86b_ncount ends (m \ K₁) ∅ := by
-- proof
  apply StatMech.Walls.gc87b_cogxg_fiber_conn ends m hnd hxg

/--
[gc87b_fiber_slack_eq_of_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean)
-/
@[path]
private lemma gc87b_fiber_slack_eq_of_allConn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {R : Finset ι}
  {o x y g : W}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hcx : connK ends R o x)
  (hcy : connK ends R o y)
  (hcg : connK ends R o g) :
-- imply
  (gc86b_ncount ends R {o, g} : ℤ) + (gc86b_ncount ends R {o, x} : ℤ) + (gc86b_ncount ends R {o, y} : ℤ) - (gc86b_ncount ends R ∅ : ℤ) = 2 * (gc86b_ncount ends R ∅ : ℤ) := by
-- proof
  apply StatMech.Walls.gc87b_fiber_slack_eq_of_allConn ends R hox hoy hog hcx hcy hcg

/--
[gc87b_slack_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean)
-/
@[path]
private lemma gc87b_slack_fiber_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  gc87b_slack ends m o x y g = ∑ K₁ ∈ m.powerset.filter (fun K => sources ends K = ∅), ((gc86b_ncount ends (m \ K₁) {o, g} : ℤ) + (gc86b_ncount ends (m \ K₁) {o, x} : ℤ) + (gc86b_ncount ends (m \ K₁) {o, y} : ℤ) - (gc86b_ncount ends (m \ K₁) ∅ : ℤ)) := by
-- proof
  apply StatMech.Walls.gc87b_slack_fiber ends m o x y g

/--
[gc87b_T3_eq_sum_if](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean)
-/
@[path]
private lemma gc87b_T3_eq_sum_if_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W} :
-- imply
  (gc87b_T3 ends m o x y g : ℤ) = ∑ K₁ ∈ m.powerset.filter (fun K => sources ends K = ∅), (if connK ends (m \ K₁) o x ∧ connK ends (m \ K₁) o y ∧ connK ends (m \ K₁) o g then (gc86b_ncount ends (m \ K₁) ∅ : ℤ) else 0) := by
-- proof
  apply StatMech.Walls.gc87b_T3_eq_sum_if ends m o x y g

/--
[gc87b_two_T3_le_slack](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean)
-/
@[path]
private lemma gc87b_two_T3_le_slack_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrc : sources ends m = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g) :
-- imply
  2 * (gc87b_T3 ends m o x y g : ℤ) ≤ gc87b_slack ends m o x y g := by
-- proof
  apply StatMech.Walls.gc87b_two_T3_le_slack ends m hnd hsrc hox hoy hog

/--
[gc87b_residual_of_cogxg_le_T3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean)
-/
@[path]
private lemma gc87b_residual_of_cogxg_le_T3_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrc : sources ends m = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hle : gc87b_CogxgLeT3 ends m o x y g) :
-- imply
  gc86b_CogxgResidual ends m o x y g := by
-- proof
  apply StatMech.Walls.gc87b_residual_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog hle

/--
[gc87b_bijection_of_cogxg_le_T3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean)
-/
@[path]
private lemma gc87b_bijection_of_cogxg_le_T3_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrc : sources ends m = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hle : gc87b_CogxgLeT3 ends m o x y g) :
-- imply
  gc85b_ThreeCurrentBijection ends m o x y g := by
-- proof
  apply StatMech.Walls.gc87b_bijection_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog hle

/--
[gc87b_tri_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean)
-/
@[path]
private lemma gc87b_tri_sources_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  sources gc87b_triEnds (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Walls.gc87b_tri_sources

/--
[gc87b_one_le_ncount_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean)
-/
@[path]
private lemma gc87b_one_le_ncount_empty_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {R : Finset ι} :
-- imply
  1 ≤ gc86b_ncount ends R ∅ := by
-- proof
  apply StatMech.Walls.gc87b_one_le_ncount_empty ends R

/--
[gc87b_one_le_T3_of_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean)
-/
@[path]
private lemma gc87b_one_le_T3_of_allConn_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hcx : connK ends m o x)
  (hcy : connK ends m o y)
  (hcg : connK ends m o g) :
-- imply
  1 ≤ gc87b_T3 ends m o x y g := by
-- proof
  apply StatMech.Walls.gc87b_one_le_T3_of_allConn ends m hcx hcy hcg

/--
[gc87b_tri_residue_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean)
-/
@[path]
private lemma gc87b_tri_residue_nonvacuous_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3} = 1 ∧ gc87b_CogxgLeT3 gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.gc87b_tri_residue_nonvacuous

/--
[gc87b_local_template_insufficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean)
-/
@[path]
private lemma gc87b_local_template_insufficient_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  ∃ (nS nT : ℕ) (adj : Fin nS → Fin nT → Prop), nS ≤ nT ∧ ∃ (fixedChoice : Fin nS → Fin nT), ¬ Function.Injective fixedChoice := by
-- proof
  apply StatMech.Walls.gc87b_local_template_insufficient

/--
[gc87b_cogxg_le_T3_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean)
-/
@[path]
private lemma gc87b_cogxg_le_T3_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrc : sources ends m = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxg : x ≠ g) :
-- imply
  (gc85b_pcount ends m {o, g} {x, g} = ∑ K₁ ∈ (m.powerset.filter (fun K => sources ends K = {o, g})).filter (fun K₁ => connK ends (m \ K₁) x g), gc86b_ncount ends (m \ K₁) ∅) ∧ (2 * (gc87b_T3 ends m o x y g : ℤ) ≤ gc87b_slack ends m o x y g) ∧ (gc87b_CogxgLeT3 ends m o x y g → gc85b_ThreeCurrentBijection ends m o x y g) := by
-- proof
  apply StatMech.Walls.gc87b_cogxg_le_T3_status ends m hnd hsrc hox hoy hog hxg


-- created on 2026-10-23
