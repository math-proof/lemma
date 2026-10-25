import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc10deltasupport
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc10_pairSum_term_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10deltasupport.lean)
-/
@[path]
private lemma gc10_pairSum_term_nonneg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {w : ℝ}
  [Decidable P]
-- given
  (hw : 0 ≤ w)
  (P : Prop) :
-- imply
  0 ≤ w * (if P then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Walls.gc10_pairSum_term_nonneg w hw P

/--
[gc10_pairSum_is_sum_of_nonneg_terms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10deltasupport.lean)
-/
@[path]
private lemma gc10_pairSum_is_sum_of_nonneg_terms_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {A : Finset V}
  {F : Finset ι → ℝ}
-- given
  (P : Finset ι → Prop)
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  drd_pairSum ends A F P = ∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A), F m * (if P m then (1 : ℝ) else 0)) ∧ 0 ≤ drd_pairSum ends A F P := by
-- proof
  apply StatMech.Walls.gc10_pairSum_is_sum_of_nonneg_terms ends A F P hF

/--
[gc10_caseA_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10deltasupport.lean)
-/
@[path]
private lemma gc10_caseA_nonneg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o x y g : V}
-- given
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m) := by
-- proof
  apply StatMech.Walls.gc10_caseA_nonneg ends F o x y g hF

/--
[gc10_caseB_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10deltasupport.lean)
-/
@[path]
private lemma gc10_caseB_nonneg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o x y g : V}
-- given
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) := by
-- proof
  apply StatMech.Walls.gc10_caseB_nonneg ends F o x y g hF

/--
[gc10_caseB_eq_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10deltasupport.lean)
-/
@[path]
private lemma gc10_caseB_eq_swap_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {o x y g : V}
  {m : Finset ι} :
-- imply
  gc8_caseB ends o x y g m = gc8_caseA ends o y x g m := by
-- proof
  apply StatMech.Walls.gc10_caseB_eq_swap ends o x y g m

/--
[gc10_delta_eq_caseA_plus_caseB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10deltasupport.lean)
-/
@[path]
private lemma gc10_delta_eq_caseA_plus_caseB_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o x y g : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
-- imply
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m) = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m) + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) := by
-- proof
  apply StatMech.Walls.gc10_delta_eq_caseA_plus_caseB ends F hox hoy hog hxy hxg hyg hnd hsrcSet

/--
[gc10_delta_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10deltasupport.lean)
-/
@[path]
private lemma gc10_delta_support_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o x y g : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hF : ∀ m, 0 ≤ F m)
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
-- imply
  (drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m) = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m) + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m)) ∧ (∀ m : Finset ι, gc8_caseB ends o x y g m = gc8_caseA ends o y x g m) ∧ (0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m)) ∧ (0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m)) ∧ (0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m)) := by
-- proof
  apply StatMech.Walls.gc10_delta_support ends F hox hoy hog hxy hxg hyg hnd hF hsrcSet

/--
[gc10_delta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10deltasupport.lean)
-/
@[path]
private lemma gc10_delta_nonneg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o x y g : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hF : ∀ m, 0 ≤ F m)
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
-- imply
  0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m) := by
-- proof
  apply StatMech.Walls.gc10_delta_nonneg ends F hox hoy hog hxy hxg hyg hnd hF hsrcSet

/--
[gc10_ferro_mass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10deltasupport.lean)
-/
@[path]
private lemma gc10_ferro_mass_nonneg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {n₁ n₂ : Sharpness.Current V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ weight G β J n₁ * weight G β J n₂ := by
-- proof
  apply StatMech.Walls.gc10_ferro_mass_nonneg G β J hβ hJ n₁ n₂

/--
[gc10_delta_support_ferro](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10deltasupport.lean)
-/
@[path]
private lemma gc10_delta_support_ferro_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {ends : ι → Sym2 V}
  {n₁ n₂ : Finset ι → Sharpness.Current V}
  {o x y g : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
-- imply
  0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) (fun m => weight G β J (n₁ m) * weight G β J (n₂ m)) (fun m => gc8_disconn ends o g m) := by
-- proof
  apply StatMech.Walls.gc10_delta_support_ferro G β J hβ hJ ends n₁ n₂ hox hoy hog hxy hxg hyg hnd hsrcSet

/--
[gc10_delta_support_uses_no_ursell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10deltasupport.lean)
-/
@[path]
private lemma gc10_delta_support_uses_no_ursell_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o x y g : V}
-- given
  (hdist : o ≠ x ∧ o ≠ y ∧ o ≠ g ∧ x ≠ y ∧ x ≠ g ∧ y ≠ g)
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hmass : ∀ m, 0 ≤ F m)
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
-- imply
  0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m) := by
-- proof
  apply StatMech.Walls.gc10_delta_support_uses_no_ursell ends F o x y g hdist hnd hmass hsrcSet

/--
[gc10_delta_support_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10deltasupport.lean)
-/
@[path]
private lemma gc10_delta_support_nonvacuous_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V] :
-- imply
  0 ≤ drd_pairSum (witEnds) ({0, 1, 2, 3} : Finset (Fin 4)) (fun _ => (1 : ℝ)) (fun m => gc8_disconn witEnds (0 : Fin 4) 3 m) := by
-- proof
  apply StatMech.Walls.gc10_delta_support_nonvacuous


-- created on 2026-10-23
