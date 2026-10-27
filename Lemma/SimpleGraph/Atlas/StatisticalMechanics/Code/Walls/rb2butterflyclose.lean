import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rb2butterflyclose.Part6
open Finset StatMech StatMech.Walls StatMech.Walls.Reimer


/--
[rb2_finrank_Q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_finrank_Q_eq
  {m : ℕ} :
-- imply
  Module.finrank ℝ (rbt_Q m → ℝ) = 2 ^ m := by
-- proof
  apply StatMech.Walls.Reimer.rb2_finrank_Q m

/--
[rb2_g2_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_g2_decomp_eq
  {x y z : Bool} :
-- imply
  rbt_g2 x y z = ∑ w : Bool, rb2_C x y w * rbt_g2 false w z := by
-- proof
  apply StatMech.Walls.Reimer.rb2_g2_decomp x y z

/--
[rb2_g_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_g_decomp_eq
  {m : ℕ}
  {x y : rbt_Q m} :
-- imply
  rbt_g x y = ∑ z : rbt_Q m, (∏ i, rb2_C (x i) (y i) (z i)) • rb2_hbasis z := by
-- proof
  apply StatMech.Walls.Reimer.rb2_g_decomp x y

/--
[rb2_hbasis_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_hbasis_off_eq
  {m : ℕ}
  {z w : rbt_Q m}
-- given
  (h : ¬ w ≤ z) :
-- imply
  rb2_hbasis z w = 0 := by
-- proof
  apply StatMech.Walls.Reimer.rb2_hbasis_off z w h

/--
[rb2_hbasis_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_hbasis_diag_eq
  {m : ℕ}
  {z : rbt_Q m} :
-- imply
  rb2_hbasis z z ≠ 0 := by
-- proof
  apply StatMech.Walls.Reimer.rb2_hbasis_diag z

/--
[rb2_hbasis_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_hbasis_indep_eq
  {m : ℕ} :
-- imply
  LinearIndependent ℝ (fun z : rbt_Q m => rb2_hbasis z) := by
-- proof
  apply StatMech.Walls.Reimer.rb2_hbasis_indep m

/--
[rb2_Cz_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_Cz_off_eq
  {x y w : Bool}
-- given
  (h : ¬ y ≤ w) :
-- imply
  ((rb2_Cz x y w : ZMod 2)) = 0 := by
-- proof
  apply StatMech.Walls.Reimer.rb2_Cz_off x y w h

/--
[rb2_Cz_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_Cz_diag_eq
  {x y : Bool} :
-- imply
  ((rb2_Cz x y y : ZMod 2)) = 1 := by
-- proof
  apply StatMech.Walls.Reimer.rb2_Cz_diag x y

/--
[rb2_blab_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_blab_inj_eq
  {m : ℕ}
  {T : Finset (rbt_Q m)} :
-- imply
  Function.Injective (rb2_blab T) := by
-- proof
  apply StatMech.Walls.Reimer.rb2_blab_inj T

/--
[rb2_M2_blockTri](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_M2_blockTri_eq
  {m : ℕ}
  {body : rbt_Q m → rbt_Q m}
  {T : Finset (rbt_Q m)} :
-- imply
  (rb2_M2 body T).BlockTriangular (rb2_blab T) := by
-- proof
  apply StatMech.Walls.Reimer.rb2_M2_blockTri body T

/--
[rb2_M2_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_M2_det_eq
  {m : ℕ}
  {body : rbt_Q m → rbt_Q m}
  {T : Finset (rbt_Q m)} :
-- imply
  (rb2_M2 body T).det = 1 := by
-- proof
  apply StatMech.Walls.Reimer.rb2_M2_det body T

/--
[rb2_Mz_det_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_Mz_det_ne_zero_eq
  {m : ℕ}
  {body : rbt_Q m → rbt_Q m}
  {T : Finset (rbt_Q m)} :
-- imply
  (rb2_Mz body T).det ≠ 0 := by
-- proof
  apply StatMech.Walls.Reimer.rb2_Mz_det_ne_zero body T

/--
[rb2_Mr_det_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_Mr_det_ne_zero_eq
  {m : ℕ}
  {body : rbt_Q m → rbt_Q m}
  {T : Finset (rbt_Q m)} :
-- imply
  (rb2_Mr body T).det ≠ 0 := by
-- proof
  apply StatMech.Walls.Reimer.rb2_Mr_det_ne_zero body T

/--
[rb2_g_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_g_indep_eq
  {m : ℕ}
  {body : rbt_Q m → rbt_Q m}
  {T : Finset (rbt_Q m)} :
-- imply
  LinearIndependent ℝ (fun y : T => rbt_g (body (y : rbt_Q m)) (y : rbt_Q m)) := by
-- proof
  apply StatMech.Walls.Reimer.rb2_g_indep body T

/--
[rb2_inner_sum_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_inner_sum_right_eq
  {m : ℕ}
  [Fintype ι]
  {A : rbt_Q m → ℝ}
  {c : ι → ℝ}
  {v : ι → (rbt_Q m → ℝ)} :
-- imply
  rbt_inner A (∑ i, c i • v i) = ∑ i, c i * rbt_inner A (v i) := by
-- proof
  apply StatMech.Walls.Reimer.rb2_inner_sum_right A c v

/--
[rb2_inner_sum_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_inner_sum_left_eq
  {m : ℕ}
  [Fintype ι]
  {c : ι → ℝ}
  {v : ι → (rbt_Q m → ℝ)}
  {A : rbt_Q m → ℝ} :
-- imply
  rbt_inner (∑ i, c i • v i) A = ∑ i, c i * rbt_inner (v i) A := by
-- proof
  apply StatMech.Walls.Reimer.rb2_inner_sum_left c v A

/--
[rb2_inner_self_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_inner_self_eq_zero_eq
  {m : ℕ}
  {A : rbt_Q m → ℝ} :
-- imply
  rbt_inner A A = 0 ↔ A = 0 := by
-- proof
  apply StatMech.Walls.Reimer.rb2_inner_self_eq_zero A

/--
[rb2_orthUnion3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_orthUnion3_eq
  {m : ℕ}
  [Fintype α]
  [Fintype β]
  [Fintype γ]
  {A : α → (rbt_Q m → ℝ)}
  {B : β → (rbt_Q m → ℝ)}
  {C : γ → (rbt_Q m → ℝ)}
-- given
  (hA : LinearIndependent ℝ A)
  (hB : LinearIndependent ℝ B)
  (hC : LinearIndependent ℝ C)
  (hAB : ∀ a b, rbt_inner (A a) (B b) = 0)
  (hAC : ∀ a c, rbt_inner (A a) (C c) = 0)
  (hBC : ∀ b c, rbt_inner (B b) (C c) = 0) :
-- imply
  LinearIndependent ℝ (Sum.elim A (Sum.elim B C)) := by
-- proof
  apply StatMech.Walls.Reimer.rb2_orthUnion3 A B C hA hB hC hAB hAC hBC

/--
[rb2_butterflyLinIndep_of_gIndep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_butterflyLinIndep_of_gIndep_eq
-- given
  (hG : rbt_G_indep) :
-- imply
  rbt_ButterflyLinIndep := by
-- proof
  apply StatMech.Walls.Reimer.rb2_butterflyLinIndep_of_gIndep hG

/--
[rb2_butterfly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_butterfly_eq
  {m : ℕ}
  {body : rbt_Q m → rbt_Q m}
  {T : Finset (rbt_Q m)}
-- given
  (hLI : rbt_ButterflyLinIndep) :
-- imply
  T.card ≤ (rbt_Red body T ∩ rbt_Yellow body T).card := by
-- proof
  apply StatMech.Walls.Reimer.rb2_butterfly hLI m body T

/--
[rb2_G_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_G_indep_eq :
-- imply
  rbt_G_indep := by
-- proof
  apply StatMech.Walls.Reimer.rb2_G_indep

/--
[rb2_butterflyLinIndep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_butterflyLinIndep_eq :
-- imply
  rbt_ButterflyLinIndep := by
-- proof
  apply StatMech.Walls.Reimer.rb2_butterflyLinIndep

/--
[rb2_butterfly_thm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb2butterflyclose.lean)
-/
@[path]
private lemma rb2_butterfly_thm_eq
  {m : ℕ}
  {body : rbt_Q m → rbt_Q m}
  {T : Finset (rbt_Q m)} :
-- imply
  T.card ≤ (rbt_Red body T ∩ rbt_Yellow body T).card := by
-- proof
  apply StatMech.Walls.Reimer.rb2_butterfly_thm m body T


-- created on 2026-10-23
