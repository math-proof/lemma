import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.DeltaRewriteDichotomy
open Finset BigOperators Classical StatMech StatMech.Sharpness


/--
[drd_deltaRewrite_perEdge_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewriteDichotomy.lean)
-/
@[path]
private lemma drd_deltaRewrite_perEdge_dichotomy_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {covTerm : ℝ}
  {o x y g : V}
-- given
  (pairSum : (Finset ι → Prop) → ℝ)
  (hpairSum_add : ∀ (P₁ P₂ : Finset ι → Prop) [DecidablePred P₁] [DecidablePred P₂] [DecidablePred (fun m => P₁ m ∨ P₂ m)], (∀ m, ¬ (P₁ m ∧ P₂ m)) → pairSum (fun m => P₁ m ∨ P₂ m) = pairSum P₁ + pairSum P₂)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hloop : ∀ m : Finset ι, ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → RandomCurrent.sources ends m = {o, x, y, g})
  (hcov : covTerm = pairSum (fun m => ¬ connK ends m o g)) :
-- imply
  covTerm = pairSum (fun m => (¬ connK ends m o g) ∧ (connK ends m o x ∧ connK ends m y g)) + pairSum (fun m => (¬ connK ends m o g) ∧ (connK ends m o y ∧ connK ends m x g)) := by
-- proof
  apply StatMech.Sharpness.drd_deltaRewrite_perEdge_dichotomy ends covTerm pairSum hpairSum_add hox hoy hog hxy hxg hyg hloop hsrcSet hcov

/--
[drd_pairSum_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewriteDichotomy.lean)
-/
@[path]
private lemma drd_pairSum_add_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {A : Finset V}
  {F : Finset ι → ℝ}
  [DecidablePred P₁]
  [DecidablePred P₂]
  [DecidablePred (fun m => P₁ m ∨ P₂ m)]
-- given
  (P₁ P₂ : Finset ι → Prop)
  (hdisj : ∀ m, ¬ (P₁ m ∧ P₂ m)) :
-- imply
  drd_pairSum ends A F (fun m => P₁ m ∨ P₂ m) = drd_pairSum ends A F P₁ + drd_pairSum ends A F P₂ := by
-- proof
  apply StatMech.Sharpness.drd_pairSum_add ends A F P₁ P₂ hdisj

/--
[drd_deltaRewrite_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewriteDichotomy.lean)
-/
@[path]
private lemma drd_deltaRewrite_full_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
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
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → RandomCurrent.sources ends m = {o, x, y, g}) :
-- imply
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => ¬ connK ends m o g) = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => (¬ connK ends m o g) ∧ (connK ends m o x ∧ connK ends m y g)) + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => (¬ connK ends m o g) ∧ (connK ends m o y ∧ connK ends m x g)) := by
-- proof
  apply StatMech.Sharpness.drd_deltaRewrite_full ends F hox hoy hog hxy hxg hyg hnd hsrcSet

/--
[drd_pairSum_disconnect_eq_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewriteDichotomy.lean)
-/
@[path]
private lemma drd_pairSum_disconnect_eq_gap_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {A : Finset V}
  {u v : V}
-- given
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (huv : u ≠ v) :
-- imply
  drd_pairSum ends A F (fun m => ¬ connK ends m u v) = (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A), F m)) - (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A ∆ {u, v}), F m)) := by
-- proof
  apply StatMech.Sharpness.drd_pairSum_disconnect_eq_gap ends F A hnd huv

/--
[drd_gap_eq_deltaForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaRewriteDichotomy.lean)
-/
@[path]
private lemma drd_gap_eq_deltaForm_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
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
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → RandomCurrent.sources ends m = {o, x, y, g}) :
-- imply
  ((∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = ({o, x, y, g} : Finset V))), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = ({o, x, y, g} : Finset V)), F m)) - (∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = ({o, x, y, g} : Finset V))), (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = ({o, x, y, g} : Finset V) ∆ {o, g}), F m))) = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => (¬ connK ends m o g) ∧ (connK ends m o x ∧ connK ends m y g)) + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => (¬ connK ends m o g) ∧ (connK ends m o y ∧ connK ends m x g)) := by
-- proof
  apply StatMech.Sharpness.drd_gap_eq_deltaForm ends F hox hoy hog hxy hxg hyg hnd hsrcSet


-- created on 2026-10-23
