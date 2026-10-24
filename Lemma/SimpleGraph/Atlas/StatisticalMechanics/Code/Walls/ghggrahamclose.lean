import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.ghggrahamclose
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[ghg_oddComp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghggrahamclose.lean)
-/
@[path]
private lemma ghg_oddComp_eq_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
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
  (compOf ends R o).filter (fun v => Odd (degK ends R v)) = insert o ((({x, y, g} : Finset W)).filter (fun w => connK ends R o w)) := by
-- proof
  apply StatMech.Walls.ghg_oddComp_eq ends R hnd hsrc hox hoy hog

/--
[ghg_conn_count_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghggrahamclose.lean)
-/
@[path]
private lemma ghg_conn_count_odd_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
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
  apply StatMech.Walls.ghg_conn_count_odd ends R hnd hsrc hox hoy hog

/--
[ghg_flux_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghggrahamclose.lean)
-/
@[path]
private lemma ghg_flux_dichotomy_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
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
  apply StatMech.Walls.ghg_flux_dichotomy ends R hnd hsrc hox hoy hog

/--
[ghg_one_or_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghggrahamclose.lean)
-/
@[path]
private lemma ghg_one_or_three_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {R : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag)
  (hsrc : sources ends R = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g) :
-- imply
  #((({x, y, g} : Finset W)).filter (fun w => connK ends R o w)) = 1 ∨ #((({x, y, g} : Finset W)).filter (fun w => connK ends R o w)) = 3 := by
-- proof
  apply StatMech.Walls.ghg_one_or_three ends R hnd hsrc hox hoy hog hxy hxg hyg

/--
[ghg_all_three_of_not_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghggrahamclose.lean)
-/
@[path]
private lemma ghg_all_three_of_not_one_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {R : Finset ι}
  {o x y g : W}
-- given
  (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag)
  (hsrc : sources ends R = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hne1 : #((({x, y, g} : Finset W)).filter (fun w => connK ends R o w)) ≠ 1) :
-- imply
  connK ends R o x ∧ connK ends R o y ∧ connK ends R o g := by
-- proof
  apply StatMech.Walls.ghg_all_three_of_not_one ends R hnd hsrc hox hoy hog hxy hxg hyg hne1

/--
[ghg_lemma2_is_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghggrahamclose.lean)
-/
@[path]
private lemma ghg_lemma2_is_switching_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {A : Finset W}
  {u v : W}
-- given
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hm : sources ends m = A)
  (huv : u ≠ v) :
-- imply
  #(m.powerset.filter (fun K => sources ends K = A ∆ {u, v})) = (if connK ends m u v then #(m.powerset.filter (fun K => sources ends K = A)) else 0) := by
-- proof
  apply StatMech.Walls.ghg_lemma2_is_switching ends m hnd A hm huv

/--
[ghg_lemma1_is_vbg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghggrahamclose.lean)
-/
@[path]
private lemma ghg_lemma1_is_vbg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β) :
-- imply
  StatMech.Ising.cov2 G β h i j * StatMech.Ising.cov2 G β h j k ≤ StatMech.Walls.VBG.vbg_var (StatMech.Ising.isingProb G β h) (fun s => StatMech.Ising.spin s j) * StatMech.Ising.cov2 G β h i k := by
-- proof
  apply StatMech.Walls.ghg_lemma1_is_vbg G β h hβ i j k

/--
[ghg_eq21_maps_to_bijection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghggrahamclose.lean)
-/
@[path]
private lemma ghg_eq21_maps_to_bijection_eq
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
  (gc85b_threeGapCount ends m o x y g ≤ 0 ↔ gc85b_ThreeCurrentBijection ends m o x y g) ∧ (gc87b_CogxgLeT3 ends m o x y g → gc85b_ThreeCurrentBijection ends m o x y g) := by
-- proof
  apply StatMech.Walls.ghg_eq21_maps_to_bijection ends m hnd hsrc hox hoy hog

/--
[ghg_tri_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghggrahamclose.lean)
-/
@[path]
private lemma ghg_tri_nonvacuous_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3} = 1 ∧ gc87b_CogxgLeT3 gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.ghg_tri_nonvacuous

/--
[ghg_graham_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghggrahamclose.lean)
-/
@[path]
private lemma ghg_graham_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.ghg_graham_status


-- created on 2026-10-23
