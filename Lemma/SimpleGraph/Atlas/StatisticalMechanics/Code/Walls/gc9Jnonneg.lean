import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.gc9Jnonneg
open Finset BigOperators SimpleGraph Set StatMech StatMech.Walls


/--
[gc9_J_summand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9Jnonneg.lean)
-/
@[path]
private lemma gc9_J_summand_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {F : Finset ι → ℝ}
  {o x y g : V}
  {Jxy : ℝ}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hF : ∀ m, 0 ≤ F m)
  (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g})
  (hJ : 0 ≤ Jxy) :
-- imply
  0 ≤ Jxy * drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m) := by
-- proof
  apply StatMech.Walls.gc9_J_summand_nonneg ends F hox hoy hog hxy hxg hyg hnd hF hsrcSet Jxy hJ

/--
[gc9_J_summand_nonneg_of_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9Jnonneg.lean)
-/
@[path]
private lemma gc9_J_summand_nonneg_of_delta_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {Jxy δxy : ℝ}
-- given
  (hJ : 0 ≤ Jxy)
  (hδ : 0 ≤ δxy) :
-- imply
  0 ≤ Jxy * δxy := by
-- proof
  apply StatMech.Walls.gc9_J_summand_nonneg_of_delta Jxy δxy hJ hδ

/--
[gc9_J_sum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9Jnonneg.lean)
-/
@[path]
private lemma gc9_J_sum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {s : Finset E}
  {J : E → ℝ}
  {δ : E → ℝ}
-- given
  (hJ : ∀ e ∈ s, 0 ≤ J e)
  (hδ : ∀ e ∈ s, 0 ≤ δ e) :
-- imply
  0 ≤ ∑ e ∈ s, J e * δ e := by
-- proof
  apply StatMech.Walls.gc9_J_sum_nonneg s J δ hJ hδ

/--
[gc9_J_sum_scaled_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9Jnonneg.lean)
-/
@[path]
private lemma gc9_J_sum_scaled_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {s : Finset E}
  {J : E → ℝ}
  {δ : E → ℝ}
  {Z : ℝ}
-- given
  (hZ : 0 < Z)
  (hJ : ∀ e ∈ s, 0 ≤ J e)
  (hδ : ∀ e ∈ s, 0 ≤ δ e) :
-- imply
  0 ≤ (1 / Z ^ 2) * ∑ e ∈ s, J e * δ e := by
-- proof
  apply StatMech.Walls.gc9_J_sum_scaled_nonneg s J δ Z hZ hJ hδ

/--
[gc9_J_deriv_eq20_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9Jnonneg.lean)
-/
@[path]
private lemma gc9_J_deriv_eq20_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq ι]
  [Fintype ι]
  {s : Finset E}
  {J : E → ℝ}
  {Z : ℝ}
  {ends : E → ι → Sym2 V}
  {F : E → Finset ι → ℝ}
  {o : V}
  {xe ye : E → V}
  {g : V}
-- given
  (hZ : 0 < Z)
  (hox : ∀ e, o ≠ xe e)
  (hoy : ∀ e, o ≠ ye e)
  (hog : o ≠ g)
  (hxy : ∀ e, xe e ≠ ye e)
  (hxg : ∀ e, xe e ≠ g)
  (hyg : ∀ e, ye e ≠ g)
  (hnd : ∀ e i, ¬ (ends e i).IsDiag)
  (hF : ∀ e m, 0 ≤ F e m)
  (hsrcSet : ∀ e (m : Finset ι), (¬ connK (ends e) m o g) → sources (ends e) m = {o, xe e, ye e, g})
  (hJ : ∀ e ∈ s, 0 ≤ J e) :
-- imply
  0 ≤ (1 / Z ^ 2) * ∑ e ∈ s, J e * drd_pairSum (ends e) ({o, xe e, ye e, g} : Finset V) (F e) (fun m => gc8_disconn (ends e) o g m) := by
-- proof
  apply StatMech.Walls.gc9_J_deriv_eq20_nonneg s J Z hZ ends F o xe ye g hox hoy hog hxy hxg hyg hnd hF hsrcSet hJ


-- created on 2026-10-23
