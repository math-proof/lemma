import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.ghbthreecurrent.Part2
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[ghb_count_reduction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghbthreecurrent.lean)
-/
@[path]
private lemma ghb_count_reduction_eq
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
  apply StatMech.Walls.ghb_count_reduction ends m hnd hsrc hox hoy hog hle

/--
[ghb_two_T3_le_slack](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghbthreecurrent.lean)
-/
@[path]
private lemma ghb_two_T3_le_slack_eq
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
  apply StatMech.Walls.ghb_two_T3_le_slack ends m hnd hsrc hox hoy hog

/--
[ghb_gks_drop_is_pairwise_at_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghbthreecurrent.lean)
-/
@[path]
private lemma ghb_gks_drop_is_pairwise_at_count_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  ∃ c00 c0og c0ox c0oy cogxg : ℤ, 0 ≤ c00 ∧ 0 ≤ c0og ∧ 0 ≤ c0ox ∧ 0 ≤ c0oy ∧ 0 ≤ cogxg ∧ cogxg ≤ c0og ∧ cogxg ≤ c0ox ∧ cogxg ≤ c0oy ∧ cogxg ≤ c00 ∧ ¬ (c00 + 2 * cogxg ≤ c0og + c0ox + c0oy) := by
-- proof
  apply StatMech.Walls.ghb_gks_drop_is_pairwise_at_count

/--
[ghb_count_shadow_insufficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghbthreecurrent.lean)
-/
@[path]
private lemma ghb_count_shadow_insufficient_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  ¬ (∀ c00 c0og c0ox c0oy cogxg : ℤ, 0 ≤ c00 → 0 ≤ c0og → 0 ≤ c0ox → 0 ≤ c0oy → 0 ≤ cogxg → cogxg ≤ c0og → cogxg ≤ c0ox → cogxg ≤ c0oy → cogxg ≤ c00 → c00 + 2 * cogxg ≤ c0og + c0ox + c0oy) := by
-- proof
  apply StatMech.Walls.ghb_count_shadow_insufficient

/--
[ghb_three_current_holds_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghbthreecurrent.lean)
-/
@[path]
private lemma ghb_three_current_holds_star_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  gc85b_ThreeCurrentBijection gc86b_starEnds (univ : Finset (Fin 4)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.ghb_three_current_holds_star

/--
[ghb_three_current_holds_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghbthreecurrent.lean)
-/
@[path]
private lemma ghb_three_current_holds_triangle_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  gc85b_ThreeCurrentBijection gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3 := by
-- proof
  apply StatMech.Walls.ghb_three_current_holds_triangle

/--
[ghb_canonical_reroute_lands](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghbthreecurrent.lean)
-/
@[path]
private lemma ghb_canonical_reroute_lands_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W]
  {ends : ι → Sym2 W}
  {m K₁ P : Finset ι}
  {o x y g : W}
-- given
  (hK₁m : K₁ ⊆ m)
  (hP : P ⊆ K₁)
  (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrc : sources ends m = ({o, x, y, g} : Finset W))
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg' : x ≠ g)
  (hyg : y ≠ g)
  (hK₁ : sources ends K₁ = ({o, g} : Finset W))
  (hPsrc : sources ends P = ({o, g} : Finset W))
  (hxg : connK ends (m \ K₁) x g) :
-- imply
  (K₁ \ P) ⊆ m ∧ sources ends (K₁ \ P) = (∅ : Finset W) ∧ connK ends (m \ (K₁ \ P)) o x ∧ connK ends (m \ (K₁ \ P)) o y ∧ connK ends (m \ (K₁ \ P)) o g := by
-- proof
  apply StatMech.Walls.ghb_canonical_reroute_lands ends hK₁m hP hnd hsrc hox hoy hog hxy hxg' hyg hK₁ hPsrc hxg

/--
[ghb_three_current_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghbthreecurrent.lean)
-/
@[path]
private lemma ghb_three_current_status_eq
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
  (gc87b_CogxgLeT3 ends m o x y g → gc85b_ThreeCurrentBijection ends m o x y g) ∧ (∃ c00 c0og c0ox c0oy cogxg : ℤ, 0 ≤ c00 ∧ 0 ≤ c0og ∧ 0 ≤ c0ox ∧ 0 ≤ c0oy ∧ 0 ≤ cogxg ∧ cogxg ≤ c0og ∧ cogxg ≤ c0ox ∧ cogxg ≤ c0oy ∧ cogxg ≤ c00 ∧ ¬ (c00 + 2 * cogxg ≤ c0og + c0ox + c0oy)) ∧ (2 * (gc87b_T3 ends m o x y g : ℤ) ≤ gc87b_slack ends m o x y g) := by
-- proof
  apply StatMech.Walls.ghb_three_current_status ends m hnd hsrc hox hoy hog

/--
[ghb_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghbthreecurrent.lean)
-/
@[path]
private lemma ghb_status_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq W]
  [Fintype W] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.ghb_status


-- created on 2026-10-23
