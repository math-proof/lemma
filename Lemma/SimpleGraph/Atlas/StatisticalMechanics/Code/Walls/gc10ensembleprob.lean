import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc10ensembleprob
open Finset BigOperators SimpleGraph Classical StatMech StatMech.Walls


/--
[gc10_pairSum_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ensembleprob.lean)
-/
@[path]
private lemma gc10_pairSum_mono_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {A : Finset V}
  {F : Finset ι → ℝ}
-- given
  (P Q : Finset ι → Prop)
  (hF : ∀ m, 0 ≤ F m)
  (hPQ : ∀ m, P m → Q m) :
-- imply
  drd_pairSum ends A F P ≤ drd_pairSum ends A F Q := by
-- proof
  apply StatMech.Walls.gc10_pairSum_mono ends A F P Q hF hPQ

/--
[gc10_partitionFunction_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ensembleprob.lean)
-/
@[path]
private lemma gc10_partitionFunction_nonneg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {o x y g : V}
  {F : Finset ι → ℝ}
-- given
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  0 ≤ gc10_partitionFunction ends o x y g F := by
-- proof
  apply StatMech.Walls.gc10_partitionFunction_nonneg ends o x y g F hF

/--
[gc10_allConnMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ensembleprob.lean)
-/
@[path]
private lemma gc10_allConnMass_nonneg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {o x y g : V}
  {F : Finset ι → ℝ}
-- given
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  0 ≤ gc10_allConnMass ends o x y g F := by
-- proof
  apply StatMech.Walls.gc10_allConnMass_nonneg ends o x y g F hF

/--
[gc10_allConnMass_le_partitionFunction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ensembleprob.lean)
-/
@[path]
private lemma gc10_allConnMass_le_partitionFunction_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {o x y g : V}
  {F : Finset ι → ℝ}
-- given
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  gc10_allConnMass ends o x y g F ≤ gc10_partitionFunction ends o x y g F := by
-- proof
  apply StatMech.Walls.gc10_allConnMass_le_partitionFunction ends o x y g F hF

/--
[gc10_allConnProb_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ensembleprob.lean)
-/
@[path]
private lemma gc10_allConnProb_eq_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {o x y g : V}
  {F : Finset ι → ℝ} :
-- imply
  gc10_allConnProb ends o x y g F = gc10_allConnMass ends o x y g F / gc10_partitionFunction ends o x y g F := by
-- proof
  apply StatMech.Walls.gc10_allConnProb_eq ends o x y g F

/--
[gc10_allConnProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ensembleprob.lean)
-/
@[path]
private lemma gc10_allConnProb_nonneg_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {o x y g : V}
  {F : Finset ι → ℝ}
-- given
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  0 ≤ gc10_allConnProb ends o x y g F := by
-- proof
  apply StatMech.Walls.gc10_allConnProb_nonneg ends o x y g F hF

/--
[gc10_allConnProb_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ensembleprob.lean)
-/
@[path]
private lemma gc10_allConnProb_le_one_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {o x y g : V}
  {F : Finset ι → ℝ}
-- given
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  gc10_allConnProb ends o x y g F ≤ 1 := by
-- proof
  apply StatMech.Walls.gc10_allConnProb_le_one ends o x y g F hF

/--
[gc10_allConnProb_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ensembleprob.lean)
-/
@[path]
private lemma gc10_allConnProb_mem_Icc_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {o x y g : V}
  {F : Finset ι → ℝ}
-- given
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  gc10_allConnProb ends o x y g F ∈ Set.Icc (0 : ℝ) 1 := by
-- proof
  apply StatMech.Walls.gc10_allConnProb_mem_Icc ends o x y g F hF

/--
[gc10_allConnMass_eq_caseA_plus_caseB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ensembleprob.lean)
-/
@[path]
private lemma gc10_allConnMass_eq_caseA_plus_caseB_eq
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
  gc10_allConnMass ends o x y g F = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m) + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) := by
-- proof
  apply StatMech.Walls.gc10_allConnMass_eq_caseA_plus_caseB ends F hox hoy hog hxy hxg hyg hnd hsrcSet

/--
[gc10_caseA_caseB_le_partitionFunction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ensembleprob.lean)
-/
@[path]
private lemma gc10_caseA_caseB_le_partitionFunction_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {o x y g : V}
  {F : Finset ι → ℝ}
-- given
  (hF : ∀ m, 0 ≤ F m) :
-- imply
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m) ≤ gc10_partitionFunction ends o x y g F ∧ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) ≤ gc10_partitionFunction ends o x y g F := by
-- proof
  apply StatMech.Walls.gc10_caseA_caseB_le_partitionFunction ends o x y g F hF

/--
[gc10_allConnProb_ferro](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ensembleprob.lean)
-/
@[path]
private lemma gc10_allConnProb_ferro_eq
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
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  gc10_allConnMass ends o x y g (fun m => weight G β J (n₁ m) * weight G β J (n₂ m)) ≤ gc10_partitionFunction ends o x y g (fun m => weight G β J (n₁ m) * weight G β J (n₂ m)) ∧ gc10_allConnProb ends o x y g (fun m => weight G β J (n₁ m) * weight G β J (n₂ m)) ∈ Set.Icc (0 : ℝ) 1 := by
-- proof
  apply StatMech.Walls.gc10_allConnProb_ferro G β J hβ hJ ends n₁ n₂ o x y g

/--
[gc10_u3_nonpos_of_ensemble](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ensembleprob.lean)
-/
@[path]
private lemma gc10_u3_nonpos_of_ensemble_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V]
  {ends : ι → Sym2 V}
  {o x y g : V}
  {F : Finset ι → ℝ}
  {u₃ : ℝ}
-- given
  (hF : ∀ m, 0 ≤ F m)
  (hid : u₃ = -2 * gc10_allConnMass ends o x y g F) :
-- imply
  u₃ ≤ 0 := by
-- proof
  apply StatMech.Walls.gc10_u3_nonpos_of_ensemble ends o x y g F hF u₃ hid

/--
[gc10_allConnProb_mem_Icc_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc10ensembleprob.lean)
-/
@[path]
private lemma gc10_allConnProb_mem_Icc_nonvacuous_eq
  [DecidableEq ι]
  [Fintype ι]
  [DecidableEq V]
  [Fintype V] :
-- imply
  gc10_allConnMass (witEnds) (0 : Fin 4) 1 2 3 (fun _ => (1 : ℝ)) ≤ gc10_partitionFunction (witEnds) (0 : Fin 4) 1 2 3 (fun _ => (1 : ℝ)) ∧ gc10_allConnProb (witEnds) (0 : Fin 4) 1 2 3 (fun _ => (1 : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
-- proof
  apply StatMech.Walls.gc10_allConnProb_mem_Icc_nonvacuous


-- created on 2026-10-23
