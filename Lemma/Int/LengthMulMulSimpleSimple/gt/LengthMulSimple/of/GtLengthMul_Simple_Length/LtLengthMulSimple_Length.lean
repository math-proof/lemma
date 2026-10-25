import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.HeckeAlgebra.Generic.Part2
open HeckeAlgebra


namespace HeckeAlgebra

/--
[length_swt_gt_sw](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generic.lean)
-/
@[path]
private lemma length_swt_gt_sw
  [Group W]
  {M : CoxeterMatrix B}
  [CommRing R]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M M.Group}
  {s t : B}
  {w : M.Group}
-- given
  (hsw : cs.length (cs.simple s * w) < cs.length w)
  (hwt : cs.length (w * cs.simple t) > cs.length w) :
-- imply
  cs.length (cs.simple s * w * cs.simple t) > cs.length (cs.simple s * w) := by
-- proof
  obtain h_up | h_down := cs.length_mul_simple (cs.simple s * w) t
  · omega
  · have key : cs.simple s * (cs.simple s * w * cs.simple t) = w * cs.simple t := by
    rw [← mul_assoc, cs.simple_mul_simple_cancel_left s]
    obtain h1 | h1 := cs.length_simple_mul (cs.simple s * w * cs.simple t) s
    · rw [key] at h1
      obtain hs1 | hs1 <;> := cs.length_simple_mul w s
        obtain ht1 | ht1 <;> omega := cs.length_mul_simple w t
    · rw [key] at h1
      obtain hs1 | hs1 <;> := cs.length_simple_mul w s
        obtain ht1 | ht1 <;> omega := cs.length_mul_simple w t

end HeckeAlgebra

namespace HeckeAlgebra

/--
[s_mul_swt_eq_wt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generic.lean)
-/
@[path]
private lemma s_mul_swt_eq_wt
  [Group W]
  {M : CoxeterMatrix B}
  [CommRing R]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M M.Group}
  {s t : B}
  {w : M.Group} :
-- imply
  cs.simple s * (cs.simple s * w * cs.simple t) = w * cs.simple t := by
-- proof
  rw [← mul_assoc, cs.simple_mul_simple_cancel_left s]

end HeckeAlgebra

namespace HeckeAlgebra

/--
[GenericAlgebra.SatisfiesLengthDownRule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generic.lean)
-/
@[path]
private lemma GenericAlgebra.SatisfiesLengthDownRule
  [Group W]
  {M : CoxeterMatrix B}
  [CommRing R]
  {A : GenericAlgebra M R} :
-- imply
  let cs := M.toCoxeterSystem ∀ (s : B) (w : M.Group), cs.length (cs.simple s * w) < cs.length w → A.mul (A.basis (cs.simple s)) (A.basis w) = A.add (A.smul (A.sc.a s) (A.basis w)) (A.smul (A.sc.b s) (A.basis (cs.simple s * w))) := by
-- proof
  intro cs s w hlength
  set sw := cs.simple s * w
  have hw : cs.simple s * sw = w := cs.simple_mul_simple_cancel_left s
  have hlength_up_sw : cs.length (cs.simple s * sw) > cs.length sw := by
    rw [hw]; exact hlength
  have h_Ts_Tsw : A.mul (A.basis (cs.simple s)) (A.basis sw) = A.basis w := by
    rw [A.length_up s sw hlength_up_sw, hw]
  calc A.mul (A.basis (cs.simple s)) (A.basis w)
    = A.mul (A.basis (cs.simple s))
      (A.mul (A.basis (cs.simple s)) (A.basis sw)) := by
      rw [h_Ts_Tsw]
    _ = A.mul (A.mul (A.basis (cs.simple s)) (A.basis (cs.simple s)))
      (A.basis sw) := by
      rw [A.gen_left_assoc]
    _ = A.mul (A.add (A.smul (A.sc.a s) (A.basis (cs.simple s)))
      (A.smul (A.sc.b s) (A.basis 1)))
      (A.basis sw) := by
      rw [A.quadratic]
    _ = A.add (A.mul (A.smul (A.sc.a s) (A.basis (cs.simple s))) (A.basis sw))
      (A.mul (A.smul (A.sc.b s) (A.basis 1)) (A.basis sw)) := by
      rw [A.mul_add_left]
    _ = A.add (A.smul (A.sc.a s) (A.mul (A.basis (cs.simple s)) (A.basis sw)))
      (A.smul (A.sc.b s) (A.mul (A.basis 1) (A.basis sw))) := by
      rw [A.smul_mul_left, A.smul_mul_left]
    _ = A.add (A.smul (A.sc.a s) (A.basis w))
      (A.smul (A.sc.b s) (A.basis sw)) := by
      rw [h_Ts_Tsw, A.identity_left]

end HeckeAlgebra

namespace HeckeAlgebra

/--
[GenericAlgebra.SatisfiesRightLengthUpRule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generic.lean)
-/
@[path]
private lemma GenericAlgebra.SatisfiesRightLengthUpRule
  [Group W]
  {M : CoxeterMatrix B}
  [CommRing R]
  {A : GenericAlgebra M R} :
-- imply
  let cs := M.toCoxeterSystem ∀ (t : B) (w : M.Group), cs.length (w * cs.simple t) > cs.length w → A.mul (A.basis w) (A.basis (cs.simple t)) = A.basis (w * cs.simple t) := by
-- proof
  intro cs t
  suffices ∀ (n : ℕ) (w : M.Group), cs.length w ≤ n →
    cs.length (w * cs.simple t) > cs.length w →
    A.mul (A.basis w) (A.basis (cs.simple t)) = A.basis (w * cs.simple t) by
    intro w hwt
    exact this (cs.length w) w le_rfl hwt
  intro n
  induction n with
  | zero =>
    intro w hw hwt
    have hw1 : w = 1 := cs.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst hw1
    simp only [one_mul]
    rw [A.identity_left]
  | succ n ih =>
    intro w hw hwt
    by_cases hw1 : w = 1
    · subst hw1; simp only [one_mul]; rw [A.identity_left]
    · obtain ⟨s, hs⟩ := cs.exists_leftDescent_of_ne_one hw1
      set sw := cs.simple s * w with sw_def
      have hsw_lt : cs.length sw < cs.length w := hs
      have hs_sw : cs.length (cs.simple s * sw) > cs.length sw := by
        rw [cs.simple_mul_simple_cancel_left s]; exact hsw_lt
      have h_TsTsw : A.mul (A.basis (cs.simple s)) (A.basis sw) = A.basis w := by
        rw [A.length_up s sw hs_sw, cs.simple_mul_simple_cancel_left s]
      have hswt_gt : cs.length (sw * cs.simple t) > cs.length sw := by
        rw [sw_def]; exact length_swt_gt_sw cs s t w hsw_lt hwt
      have h_ind : A.mul (A.basis sw) (A.basis (cs.simple t)) =
        A.basis (sw * cs.simple t) := by
        apply ih sw; omega; exact hswt_gt
      have hs_swt : cs.length (cs.simple s * (sw * cs.simple t)) >
        cs.length (sw * cs.simple t) := by
        rw [sw_def, s_mul_swt_eq_wt cs s t w]
        obtain h | h <;> := cs.length_simple_mul w s
          obtain h' | h' <;> := cs.length_mul_simple w t
          obtain h'' | h'' <;> := cs.length_mul_simple (cs.simple s * w) t
          (rw [sw_def] at hsw_lt hswt_gt; omega)
      calc A.mul (A.basis w) (A.basis (cs.simple t))
        = A.mul (A.mul (A.basis (cs.simple s)) (A.basis sw))
          (A.basis (cs.simple t)) := by rw [h_TsTsw]
        _ = A.mul (A.basis (cs.simple s))
          (A.mul (A.basis sw) (A.basis (cs.simple t))) := by
          rw [← A.gen_left_assoc]
        _ = A.mul (A.basis (cs.simple s)) (A.basis (sw * cs.simple t)) := by
          rw [h_ind]
        _ = A.basis (cs.simple s * (sw * cs.simple t)) := by
          rw [A.length_up s (sw * cs.simple t) hs_swt]
        _ = A.basis (w * cs.simple t) := by
          rw [sw_def, s_mul_swt_eq_wt cs s t w]

end HeckeAlgebra

namespace HeckeAlgebra

/--
[GenericAlgebra.basis_left_mul_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generic.lean)
-/
@[path]
private lemma GenericAlgebra.basis_left_mul_assoc
  [Group W]
  {M : CoxeterMatrix B}
  [CommRing R]
  {A : GenericAlgebra M R} :
-- imply
  let _cs := M.toCoxeterSystem ∀ (w : M.Group) (y z : A.carrier), A.mul (A.basis w) (A.mul y z) = A.mul (A.mul (A.basis w) y) z := by
-- proof
  intro cs
  suffices ∀ (n : ℕ) (w : M.Group), cs.length w ≤ n →
    ∀ (y z : A.carrier),
      A.mul (A.basis w) (A.mul y z) = A.mul (A.mul (A.basis w) y) z by
    intro w y z
    exact this (cs.length w) w le_rfl y z
  intro n
  induction n with
  | zero =>
    intro w hw y z
    have hw1 : w = 1 := cs.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst hw1
    simp only [A.identity_left]
  | succ n ih =>
    intro w hw y z
    by_cases hw1 : w = 1
    · subst hw1; simp only [A.identity_left]
    · obtain ⟨s, hs⟩ := cs.exists_leftDescent_of_ne_one hw1
      set sw := cs.simple s * w
      have hsw_lt : cs.length sw < cs.length w := hs
      have hs_sw : cs.length (cs.simple s * sw) > cs.length sw := by
        rw [cs.simple_mul_simple_cancel_left s]; exact hsw_lt
      have h_basis_w : A.basis w = A.mul (A.basis (cs.simple s)) (A.basis sw) := by
        rw [A.length_up s sw hs_sw, cs.simple_mul_simple_cancel_left s]
      calc A.mul (A.basis w) (A.mul y z)
        = A.mul (A.mul (A.basis (cs.simple s)) (A.basis sw)) (A.mul y z) := by
          rw [← h_basis_w]
        _ = A.mul (A.basis (cs.simple s)) (A.mul (A.basis sw) (A.mul y z)) := by
          rw [← A.gen_left_assoc]
        _ = A.mul (A.basis (cs.simple s)) (A.mul (A.mul (A.basis sw) y) z) := by
          rw [ih sw (by omega) y z]
        _ = A.mul (A.mul (A.basis (cs.simple s)) (A.mul (A.basis sw) y)) z := by
          rw [A.gen_left_assoc]
        _ = A.mul (A.mul (A.mul (A.basis (cs.simple s)) (A.basis sw)) y) z := by
          rw [A.gen_left_assoc]
        _ = A.mul (A.mul (A.basis w) y) z := by
          rw [← h_basis_w]

end HeckeAlgebra

namespace HeckeAlgebra

/--
[GenericAlgebra.mul_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generic.lean)
-/
@[path]
private lemma GenericAlgebra.mul_assoc
  [Group W]
  {M : CoxeterMatrix B}
  [CommRing R]
  {A : GenericAlgebra M R} :
-- imply
  ∀ x y z, A.mul (A.mul x y) z = A.mul x (A.mul y z) := by
-- proof
  suffices ∀ x, ∀ y z, A.mul (A.mul x y) z = A.mul x (A.mul y z) by
    intro x y z; exact this x y z
  apply A.basis_span (fun x => ∀ y z, A.mul (A.mul x y) z = A.mul x (A.mul y z))
  ·
    intro w y z
    exact (A.basis_left_mul_assoc w y z).symm
  ·
    intro x₁ x₂ hx₁ hx₂ y z
    calc A.mul (A.mul (A.add x₁ x₂) y) z
      = A.mul (A.add (A.mul x₁ y) (A.mul x₂ y)) z := by rw [A.mul_add_left]
      _ = A.add (A.mul (A.mul x₁ y) z) (A.mul (A.mul x₂ y) z) := by rw [A.mul_add_left]
      _ = A.add (A.mul x₁ (A.mul y z)) (A.mul x₂ (A.mul y z)) := by rw [hx₁, hx₂]
      _ = A.mul (A.add x₁ x₂) (A.mul y z) := by rw [A.mul_add_left]
  ·
    intro r x hx y z
    calc A.mul (A.mul (A.smul r x) y) z
      = A.mul (A.smul r (A.mul x y)) z := by rw [A.smul_mul_left]
      _ = A.smul r (A.mul (A.mul x y) z) := by rw [A.smul_mul_left]
      _ = A.smul r (A.mul x (A.mul y z)) := by rw [hx]
      _ = A.mul (A.smul r x) (A.mul y z) := by rw [A.smul_mul_left]

end HeckeAlgebra

namespace HeckeAlgebra

/--
[GenericAlgebra.SatisfiesRightLengthDownRule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/HeckeAlgebra/Generic.lean)
-/
@[path]
private lemma GenericAlgebra.SatisfiesRightLengthDownRule
  [Group W]
  {M : CoxeterMatrix B}
  [CommRing R]
  {A : GenericAlgebra M R} :
-- imply
  let cs := M.toCoxeterSystem ∀ (s : B) (w : M.Group), cs.length (w * cs.simple s) < cs.length w → A.mul (A.basis w) (A.basis (cs.simple s)) = A.add (A.smul (A.sc.a s) (A.basis w)) (A.smul (A.sc.b s) (A.basis (w * cs.simple s))) := by
-- proof
  intro cs s w hlength
  set ws := w * cs.simple s
  have hw : ws * cs.simple s = w := by
    show w * cs.simple s * cs.simple s = w
    exact cs.simple_mul_simple_cancel_right s
  have hlen_ws : cs.length (ws * cs.simple s) > cs.length ws := by
    rw [hw]; exact hlength
  have h_Tws_Ts : A.mul (A.basis ws) (A.basis (cs.simple s)) = A.basis w := by
    rw [A.SatisfiesRightLengthUpRule s ws hlen_ws, hw]
  calc A.mul (A.basis w) (A.basis (cs.simple s))
    = A.mul (A.mul (A.basis ws) (A.basis (cs.simple s)))
      (A.basis (cs.simple s)) := by
      rw [h_Tws_Ts]
    _ = A.mul (A.basis ws)
      (A.mul (A.basis (cs.simple s)) (A.basis (cs.simple s))) := by
      rw [A.mul_assoc]
    _ = A.mul (A.basis ws)
      (A.add (A.smul (A.sc.a s) (A.basis (cs.simple s)))
        (A.smul (A.sc.b s) (A.basis 1))) := by
      rw [A.quadratic]
    _ = A.add (A.mul (A.basis ws) (A.smul (A.sc.a s) (A.basis (cs.simple s))))
      (A.mul (A.basis ws) (A.smul (A.sc.b s) (A.basis 1))) := by
      rw [A.mul_add_right]
    _ = A.add (A.smul (A.sc.a s) (A.mul (A.basis ws) (A.basis (cs.simple s))))
      (A.smul (A.sc.b s) (A.mul (A.basis ws) (A.basis 1))) := by
      rw [A.mul_smul_right, A.mul_smul_right]
    _ = A.add (A.smul (A.sc.a s) (A.basis w))
      (A.smul (A.sc.b s) (A.basis ws)) := by
      rw [h_Tws_Ts, A.identity_right]

end HeckeAlgebra


-- created on 2026-10-23
-- updated on 2026-10-24
