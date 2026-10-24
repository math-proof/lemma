import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.JaccardLattice
open JaccardLattice


namespace JaccardLattice

variable [Lattice L]
/--
[modularAndMonotone_of_gilbertCondition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/JaccardLattice.lean)
-/
@[path]
private lemma modularAndMonotone_of_gilbertCondition {f : L → ℝ}
  (hG : GilbertCondition f) : IsModularValuation f ∧ Monotone f := by
  have low : ∀ P Q : L, f P + f Q ≥ f (P ⊔ Q) + f (P ⊓ Q) := by
    intro P Q
    have hg := hG P Q (P ⊓ Q)
    have s1 : P ⊔ (P ⊓ Q) = P :=
      le_antisymm (sup_le le_rfl inf_le_left) le_sup_left
    have s2 : (P ⊓ Q) ⊔ Q = Q :=
      le_antisymm (sup_le inf_le_right le_rfl) le_sup_right
    have s3 : P ⊓ (P ⊓ Q) = P ⊓ Q :=
      le_antisymm inf_le_right (le_inf inf_le_left le_rfl)
    have s4 : (P ⊓ Q) ⊓ Q = P ⊓ Q :=
      le_antisymm inf_le_left (le_inf le_rfl inf_le_right)
    have s5 : P ⊔ Q ⊔ (P ⊓ Q) = P ⊔ Q :=
      le_antisymm (sup_le le_rfl (le_trans inf_le_left le_sup_left)) le_sup_left
    rw [s1, s2, s3, s4, s5] at hg
    linarith
  have high : ∀ P Q : L, f (P ⊔ Q) + f (P ⊓ Q) ≥ f P + f Q := by
    intro P Q
    have hg := hG P Q (P ⊔ Q)
    have t1 : P ⊔ (P ⊔ Q) = P ⊔ Q :=
      le_antisymm (sup_le le_sup_left le_rfl) le_sup_right
    have t2 : (P ⊔ Q) ⊔ Q = P ⊔ Q :=
      le_antisymm (sup_le le_rfl le_sup_right) le_sup_left
    have t3 : P ⊓ (P ⊔ Q) = P :=
      le_antisymm inf_le_left (le_inf le_rfl le_sup_left)
    have t4 : (P ⊔ Q) ⊓ Q = Q :=
      le_antisymm inf_le_right (le_inf le_sup_right le_rfl)
    have t5 : P ⊔ Q ⊔ (P ⊔ Q) = P ⊔ Q :=
      le_antisymm (sup_le le_rfl le_rfl) le_sup_left
    rw [t1, t2, t3, t4, t5] at hg
    linarith
  have hmod : IsModularValuation f := by
    intro P Q
    have a1 := low P Q
    have a2 := high P Q
    linarith
  have hmono : Monotone f := by
    intro P Q hPQ
    have hg := hG Q Q P
    have w1 : Q ⊔ P = Q := le_antisymm (sup_le le_rfl hPQ) le_sup_left
    have w2 : P ⊔ Q = Q := le_antisymm (sup_le hPQ le_rfl) le_sup_right
    have w3 : Q ⊓ Q = Q := le_antisymm inf_le_left (le_inf le_rfl le_rfl)
    have w4 : Q ⊓ P = P := le_antisymm inf_le_right (le_inf hPQ le_rfl)
    have w5 : P ⊓ Q = P := le_antisymm inf_le_left (le_inf le_rfl hPQ)
    have w6 : Q ⊔ Q ⊔ P = Q :=
      le_antisymm (sup_le (sup_le le_rfl le_rfl) hPQ)
        (le_trans le_sup_left le_sup_left)
    rw [w1, w2, w3, w4, w5, w6] at hg
    linarith
  exact ⟨hmod, hmono⟩

end JaccardLattice

namespace JaccardLattice

variable [Lattice L]
/--
[gilbertCondition_of_modularAndMonotone](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/JaccardLattice.lean)
-/
@[path]
private lemma gilbertCondition_of_modularAndMonotone {f : L → ℝ}
  (hM : IsModularValuation f) (hmono : Monotone f) : GilbertCondition f := by
  intro X Y Z
  have r1 : f (X ⊔ Z) + f Y = f (X ⊔ Y ⊔ Z) + f ((X ⊔ Z) ⊓ Y) := by
    have h := hM (X ⊔ Z) Y
    have hj : (X ⊔ Z) ⊔ Y = X ⊔ Y ⊔ Z := by
      rw [sup_assoc, sup_comm Z Y, ← sup_assoc]
    rw [hj] at h
    linarith
  have r2 : f (X ⊓ Z) + f Y = f ((X ⊓ Z) ⊔ Y) + f (X ⊓ Y ⊓ Z) := by
    have h := hM (X ⊓ Z) Y
    have hm : (X ⊓ Z) ⊓ Y = X ⊓ Y ⊓ Z := by
      rw [inf_assoc, inf_comm Z Y, ← inf_assoc]
    rw [hm] at h
    linarith
  have n1 : f ((X ⊓ Z) ⊔ Y) ≤ f (Z ⊔ Y) :=
    hmono (sup_le_sup inf_le_right le_rfl)
  have n2 : f (Z ⊓ Y) ≤ f ((X ⊔ Z) ⊓ Y) :=
    hmono (inf_le_inf le_sup_right le_rfl)
  have n3 : f (X ⊓ Y ⊓ Z) ≤ f (X ⊓ Y) := hmono inf_le_left
  linarith

end JaccardLattice

namespace JaccardLattice

/--
[gilbertCondition_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/JaccardLattice.lean)
-/
@[path]
lemma gilbertCondition_iff
  [Lattice L]
  {f : L → ℝ} :
-- imply
  GilbertCondition f ↔ IsModularValuation f ∧ Monotone f :=
-- proof
  ⟨modularAndMonotone_of_gilbertCondition,
    fun h => gilbertCondition_of_modularAndMonotone h.1 h.2⟩

end JaccardLattice

namespace JaccardLattice

/--
[jaccardDist_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/JaccardLattice.lean)
-/
@[path]
lemma jaccardDist_eq_div
  [Lattice L]
  {f : L → ℝ}
  {X Y : L}
-- given
  (hpos : IsStrictlyPositive f) :
-- imply
  jaccardDist f X Y = (f (X ⊔ Y) - f (X ⊓ Y)) / f (X ⊔ Y) := by
-- proof
  unfold jaccardDist
  have hne : f (X ⊔ Y) ≠ 0 := ne_of_gt (hpos _)
  rw [← div_self hne, ← sub_div]

end JaccardLattice

namespace JaccardLattice

/--
[jaccardDist_triangle_of_gilbertCondition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/JaccardLattice.lean)
-/
@[path]
lemma jaccardDist_triangle_of_gilbertCondition
  [Lattice L]
  {f : L → ℝ}
  {U V W : L}
-- given
  (hG : GilbertCondition f)
  (hpos : IsStrictlyPositive f) :
-- imply
  jaccardDist f U W + jaccardDist f W V ≥ jaccardDist f U V := by
-- proof
  have hmono : Monotone f := (modularAndMonotone_of_gilbertCondition hG).2
  have hT : 0 < f (U ⊔ V ⊔ W) := hpos _
  have hUV : 0 < f (U ⊔ V) := hpos _
  have hUW : 0 < f (U ⊔ W) := hpos _
  have hWV : 0 < f (W ⊔ V) := hpos _
  have cUV : f (U ⊔ V) ≤ f (U ⊔ V ⊔ W) := hmono le_sup_left
  have cUW : f (U ⊔ W) ≤ f (U ⊔ V ⊔ W) :=
    hmono (sup_le (le_trans le_sup_left le_sup_left) le_sup_right)
  have cWV : f (W ⊔ V) ≤ f (U ⊔ V ⊔ W) :=
    hmono (sup_le le_sup_right (le_trans le_sup_right le_sup_left))
  have zUW : 0 ≤ f (U ⊔ W) - f (U ⊓ W) :=
    sub_nonneg.mpr (hmono (le_trans inf_le_left le_sup_left))
  have zWV : 0 ≤ f (W ⊔ V) - f (W ⊓ V) :=
    sub_nonneg.mpr (hmono (le_trans inf_le_left le_sup_left))
  have zUV : 0 ≤ f (U ⊓ V) := le_of_lt (hpos _)
  have loUW : (f (U ⊔ W) - f (U ⊓ W)) / f (U ⊔ V ⊔ W) ≤ jaccardDist f U W := by
    rw [jaccardDist_eq_div hpos U W, div_le_div_iff₀ hT hUW]
    exact mul_le_mul_of_nonneg_left cUW zUW
  have loWV : (f (W ⊔ V) - f (W ⊓ V)) / f (U ⊔ V ⊔ W) ≤ jaccardDist f W V := by
    rw [jaccardDist_eq_div hpos W V, div_le_div_iff₀ hT hWV]
    exact mul_le_mul_of_nonneg_left cWV zWV
  have upUV : jaccardDist f U V ≤
    (f (U ⊔ V ⊔ W) - f (U ⊓ V)) / f (U ⊔ V ⊔ W) := by
    have hd : f (U ⊓ V) / f (U ⊔ V ⊔ W) ≤ f (U ⊓ V) / f (U ⊔ V) := by
      rw [div_le_div_iff₀ hT hUV]
      exact mul_le_mul_of_nonneg_left cUV zUV
    have he : (f (U ⊔ V ⊔ W) - f (U ⊓ V)) / f (U ⊔ V ⊔ W)
      = 1 - f (U ⊓ V) / f (U ⊔ V ⊔ W) := by
      rw [sub_div, div_self (ne_of_gt hT)]
    unfold jaccardDist
    rw [he]
    linarith
  have hg3 := hG U V W
  have hsum : (f (U ⊔ V ⊔ W) - f (U ⊓ V)) / f (U ⊔ V ⊔ W)
    ≤ (f (U ⊔ W) - f (U ⊓ W)) / f (U ⊔ V ⊔ W)
      + (f (W ⊔ V) - f (W ⊓ V)) / f (U ⊔ V ⊔ W) := by
    rw [← add_div, div_le_div_iff_of_pos_right hT]
    linarith
  linarith

end JaccardLattice

namespace JaccardLattice

/--
[jaccardDist_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/JaccardLattice.lean)
-/
@[path]
lemma jaccardDist_triangle
  [Lattice L]
  {f : L → ℝ}
  {U V W : L}
-- given
  (hM : IsModularValuation f)
  (hmono : Monotone f)
  (hpos : IsStrictlyPositive f) :
-- imply
  jaccardDist f U W + jaccardDist f W V ≥ jaccardDist f U V :=
-- proof
  jaccardDist_triangle_of_gilbertCondition
    (gilbertCondition_of_modularAndMonotone hM hmono) hpos U V W

end JaccardLattice


-- created on 2026-10-20
-- updated on 2026-10-23
