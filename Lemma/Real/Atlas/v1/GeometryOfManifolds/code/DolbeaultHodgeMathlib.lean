import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.DolbeaultHodgeMathlib.Part2
open ContinuousAlternatingMap DolbeaultHodgeMathlib


namespace DolbeaultHodgeMathlib

/--
[L2InnerProduct.inner_eq_mathlibInner](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DolbeaultHodgeMathlib.lean)
-/
@[path]
lemma L2InnerProduct.inner_eq_mathlibInner
  {n : ℕ}
  {ip : L2InnerProduct n}
  {k : ℕ}
  {α β : DiffForm n k} :
-- imply
  ip.inner α β = @Inner.inner ℝ (DiffForm n k) (ip.toInnerProductSpace k).toInner α β := by
-- proof
  rfl

end DolbeaultHodgeMathlib

namespace DolbeaultHodgeMathlib

/--
[harmonic_is_delbar_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DolbeaultHodgeMathlib.lean)
-/
@[path]
lemma harmonic_is_delbar_closed
  {n : ℕ}
  {ip : L2InnerProduct n}
  {dol : DolbeaultData n}
  {k : ℕ}
-- given
  (hadj : HasDelbarAdjoint ip dol)
  (h : DiffForm n (k + 1))
  (hBox : dol.box_bar h = 0) :
-- imply
  dol.delbar h = 0 := by
-- proof
  have hzero : ip.inner (dol.box_bar h) h = 0 := by
    rw [hBox]
    have : (0 : DiffForm n (k + 1)) = (0 : ℝ) • h := by simp [zero_smul]
    rw [this, ip.inner_smul_left]; ring
  rw [dol.box_bar_eq, ip.inner_add_left] at hzero
  have e1 := hadj.adj (dol.delbar_star h) h
  have e2 : ip.inner (dol.delbar_star (dol.delbar h)) h =
    ip.inner (dol.delbar h) (dol.delbar h) := by
    rw [ip.inner_symm]; exact (hadj.adj h (dol.delbar h)).symm
  rw [e1, e2] at hzero
  have n1 : (0 : ℝ) ≤ ip.inner (dol.delbar_star h) (dol.delbar_star h) :=
    ip.inner_self_nonneg _
  have n2 : (0 : ℝ) ≤ ip.inner (dol.delbar h) (dol.delbar h) := ip.inner_self_nonneg _
  exact ip.inner_self_eq_zero _ (by linarith)

end DolbeaultHodgeMathlib

namespace DolbeaultHodgeMathlib

/--
[harmonic_is_delbar_star_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DolbeaultHodgeMathlib.lean)
-/
@[path]
lemma harmonic_is_delbar_star_zero
  {n : ℕ}
  {ip : L2InnerProduct n}
  {dol : DolbeaultData n}
  {k : ℕ}
-- given
  (hadj : HasDelbarAdjoint ip dol)
  (h : DiffForm n (k + 1))
  (hBox : dol.box_bar h = 0) :
-- imply
  dol.delbar_star h = 0 := by
-- proof
  have hzero : ip.inner (dol.box_bar h) h = 0 := by
    rw [hBox]
    have : (0 : DiffForm n (k + 1)) = (0 : ℝ) • h := by simp [zero_smul]
    rw [this, ip.inner_smul_left]; ring
  rw [dol.box_bar_eq, ip.inner_add_left] at hzero
  have e1 := hadj.adj (dol.delbar_star h) h
  have e2 : ip.inner (dol.delbar_star (dol.delbar h)) h =
    ip.inner (dol.delbar h) (dol.delbar h) := by
    rw [ip.inner_symm]; exact (hadj.adj h (dol.delbar h)).symm
  rw [e1, e2] at hzero
  have n1 : (0 : ℝ) ≤ ip.inner (dol.delbar_star h) (dol.delbar_star h) :=
    ip.inner_self_nonneg _
  have n2 : (0 : ℝ) ≤ ip.inner (dol.delbar h) (dol.delbar h) := ip.inner_self_nonneg _
  exact ip.inner_self_eq_zero _ (by linarith)

end DolbeaultHodgeMathlib

namespace DolbeaultHodgeMathlib

/--
[box_bar_harmonic_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DolbeaultHodgeMathlib.lean)
-/
@[path]
lemma box_bar_harmonic_unique
  {n : ℕ}
  {ip : L2InnerProduct n}
  {dol : DolbeaultData n}
  {k : ℕ}
  {a b : DiffForm n k}
-- given
  (hadj : HasDelbarAdjoint ip dol)
  (h₁ h₂ : DiffForm n (k + 1))
  (hHarm₁ : dol.box_bar h₁ = 0)
  (hHarm₂ : dol.box_bar h₂ = 0)
  (hcohom : h₁ + dol.delbar a = h₂ + dol.delbar b) :
-- imply
  h₁ = h₂ := by
-- proof
  have hstar1 := harmonic_is_delbar_star_zero ip dol hadj h₁ hHarm₁
  have hstar2 := harmonic_is_delbar_star_zero ip dol hadj h₂ hHarm₂
  have hdiff : h₁ - h₂ = dol.delbar b - dol.delbar a := by
    have h1 : h₁ - h₂ = (h₁ + dol.delbar a) - (h₂ + dol.delbar a) := by abel
    have h2 : dol.delbar b - dol.delbar a = (h₂ + dol.delbar b) - (h₂ + dol.delbar a) := by abel
    rw [h1, h2, hcohom]
  have hdelbar_sub : dol.delbar b - dol.delbar a = dol.delbar (b + (-1 : ℝ) • a) := by
    rw [dol.delbar_add, dol.delbar_smul]; simp [sub_eq_add_neg]
  have hsub_eq : h₁ - h₂ = h₁ + ((-1 : ℝ) • h₂) := by simp [sub_eq_add_neg]
  have hstar_diff : dol.delbar_star (h₁ - h₂) = 0 := by
    rw [hsub_eq, dol.delbar_star_add, dol.delbar_star_smul, hstar1, hstar2, smul_zero, add_zero]
  have hstar_delbar : dol.delbar_star (dol.delbar (b + (-1 : ℝ) • a)) = 0 := by
    rw [← hdelbar_sub, ← hdiff]; exact hstar_diff
  suffices hinner_zero : ip.inner (h₁ - h₂) (h₁ - h₂) = 0 from
    sub_eq_zero.mp (ip.inner_self_eq_zero _ hinner_zero)
  conv_lhs => rw [hdiff, hdelbar_sub]
  rw [ip.inner_symm, hadj.adj, hstar_delbar, ip.inner_symm]
  have : (0 : DiffForm n k) = (0 : ℝ) • (b + (-1 : ℝ) • a) := by simp [zero_smul]
  rw [this, ip.inner_smul_left]; ring
/-- Existence in Hodge–Dolbeault decomposition: every $\bar\partial$-closed form $\alpha$ has
a decomposition $\alpha = h + \bar\partial \beta$ with $h$ harmonic ($\bar\square h = 0$). -/

end DolbeaultHodgeMathlib


-- created on 2026-10-23
