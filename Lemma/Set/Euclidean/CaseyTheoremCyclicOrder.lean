import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[dist_sq_of_angles](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/CaseyTheoremCyclicOrder.lean)
-/
@[path]
private lemma dist_sq_of_angles {O c1 c2 : EuclideanSpace ℝ (Fin 2)} {θ1 θ2 : ℝ}
  (hc1 : c1 - O = dist c1 O • !₂[Real.cos θ1, Real.sin θ1])
  (hc2 : c2 - O = dist c2 O • !₂[Real.cos θ2, Real.sin θ2]) :
  dist c1 c2 ^ 2 = dist c1 O ^ 2 + dist c2 O ^ 2
    - 2 * dist c1 O * dist c2 O * Real.cos (θ2 - θ1) := by
  have hsub : c2 - c1 = dist c2 O • !₂[Real.cos θ2, Real.sin θ2]
    - dist c1 O • !₂[Real.cos θ1, Real.sin θ1] := by
    have h : c2 - c1 = (c2 - O) - (c1 - O) := by abel
    rw [h, hc2, hc1]
  have hnorm : ‖(dist c2 O • !₂[Real.cos θ2, Real.sin θ2]
    - dist c1 O • !₂[Real.cos θ1, Real.sin θ1] : EuclideanSpace ℝ (Fin 2))‖ ^ 2
    = (dist c2 O * Real.cos θ2 - dist c1 O * Real.cos θ1) ^ 2
    + (dist c2 O * Real.sin θ2 - dist c1 O * Real.sin θ1) ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (by positivity)]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
  rw [dist_comm c1 c2, dist_eq_norm, hsub, hnorm]
  have hcos : Real.cos θ1 * Real.cos θ2 + Real.sin θ1 * Real.sin θ2
    = Real.cos (θ2 - θ1) := by
    rw [Real.cos_sub]; ring
  have h1 : Real.cos θ1 ^ 2 + Real.sin θ1 ^ 2 = 1 := Real.cos_sq_add_sin_sq θ1
  have h2 : Real.cos θ2 ^ 2 + Real.sin θ2 ^ 2 = 1 := Real.cos_sq_add_sin_sq θ2
  linear_combination dist c2 O ^ 2 * h2 + dist c1 O ^ 2 * h1
    - 2 * dist c1 O * dist c2 O * hcos

end MetaMathlibExt

namespace MetaMathlibExt

/--
[tangent_eq_of_dist](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/CaseyTheoremCyclicOrder.lean)
-/
@[path]
private lemma tangent_eq_of_dist {R D t d1 d2 r1 r2 Δ : ℝ}
  (hd1pos : 0 < d1) (hd2pos : 0 < d2)
  (he1 : d1 = R - r1) (he2 : d2 = R - r2)
  (hD : D ^ 2 = d1 ^ 2 + d2 ^ 2 - 2 * d1 * d2 * Real.cos Δ)
  (ht : t ^ 2 = D ^ 2 - (r1 - r2) ^ 2)
  (htpos : 0 < t)
  (hΔ1 : 0 < Δ) (hΔ2 : Δ < 2 * Real.pi) :
  t = 2 * √((R - r1) * (R - r2)) * Real.sin (Δ / 2) := by
  have hA1 : (0:ℝ) < R - r1 := by rw [← he1]; exact hd1pos
  have hA2 : (0:ℝ) < R - r2 := by rw [← he2]; exact hd2pos
  have hsin : (0:ℝ) < Real.sin (Δ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · have hpi := Real.pi_pos; linarith
  have hS : (√((R - r1) * (R - r2))) ^ 2 = (R - r1) * (R - r2) :=
    Real.sq_sqrt (le_of_lt (mul_pos hA1 hA2))
  have hsin2 : Real.sin (Δ / 2) ^ 2 = 1 / 2 - Real.cos Δ / 2 := by
    have h := Real.sin_sq_eq_half_sub (Δ / 2)
    have h2 : (2:ℝ) * (Δ / 2) = Δ := by ring
    rwa [h2] at h
  have hSring : (R - r1) ^ 2 + (R - r2) ^ 2 - (r1 - r2) ^ 2
    = 2 * ((R - r1) * (R - r2)) := by ring
  have hsq : t ^ 2 = (2 * √((R - r1) * (R - r2)) * Real.sin (Δ / 2)) ^ 2 := by
    rw [ht, hD, he1, he2]
    linear_combination -4 * (Real.sin (Δ / 2)) ^ 2 * hS
      - 4 * ((R - r1) * (R - r2)) * hsin2 + hSring
  have hRHSpos : (0:ℝ) < 2 * √((R - r1) * (R - r2)) * Real.sin (Δ / 2) := by
    have hSpos : (0:ℝ) < √((R - r1) * (R - r2)) :=
      Real.sqrt_pos.mpr (mul_pos hA1 hA2)
    have h2 : (0:ℝ) < 2 * √((R - r1) * (R - r2)) := by linarith
    linarith [mul_pos h2 hsin]
  obtain h | h := (sq_eq_sq_iff_eq_or_eq_neg.mp hsq)
  · exact h
  · linarith

end MetaMathlibExt

namespace MetaMathlibExt

/--
[trig_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/CaseyTheoremCyclicOrder.lean)
-/
@[path]
private lemma trig_aux {a b c : ℝ} :
  Real.sin (a / 2) * Real.sin (c / 2)
    + Real.sin (b / 2) * Real.sin ((a + b + c) / 2)
  = Real.sin ((a + b) / 2) * Real.sin ((b + c) / 2) := by
  have p1 := Real.two_mul_sin_mul_sin (a / 2) (c / 2)
  have p2 := Real.two_mul_sin_mul_sin (b / 2) ((a + b + c) / 2)
  have p3 := Real.two_mul_sin_mul_sin ((a + b) / 2) ((b + c) / 2)
  have e1 : a / 2 - c / 2 = (a + b) / 2 - (b + c) / 2 := by ring
  have e2 : b / 2 - (a + b + c) / 2 = -(a / 2 + c / 2) := by ring
  have e3 : b / 2 + (a + b + c) / 2 = (a + b) / 2 + (b + c) / 2 := by ring
  rw [e1] at p1
  rw [e2, Real.cos_neg] at p2
  rw [e3] at p2
  linear_combination (p1 + p2 - p3) / 2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[casey_theorem_cyclic_order_core](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/CaseyTheoremCyclicOrder.lean)
-/
@[path]
lemma casey_theorem_cyclic_order_core
  {O c1 c2 c3 c4 : EuclideanSpace ℝ (Fin 2)}
  {R r1 r2 r3 r4 t12 t23 t34 t41 t13 t24 θ1 θ2 θ3 θ4 : ℝ}
-- given
  (hlt1 : r1 < R)
  (hlt2 : r2 < R)
  (hlt3 : r3 < R)
  (hlt4 : r4 < R)
  (hinner1 : dist c1 O + r1 = R)
  (hinner2 : dist c2 O + r2 = R)
  (hinner3 : dist c3 O + r3 = R)
  (hinner4 : dist c4 O + r4 = R)
  (ht12 : t12 ^ 2 = dist c1 c2 ^ 2 - (r1 - r2) ^ 2)
  (ht23 : t23 ^ 2 = dist c2 c3 ^ 2 - (r2 - r3) ^ 2)
  (ht34 : t34 ^ 2 = dist c3 c4 ^ 2 - (r3 - r4) ^ 2)
  (ht41 : t41 ^ 2 = dist c4 c1 ^ 2 - (r4 - r1) ^ 2)
  (ht13 : t13 ^ 2 = dist c1 c3 ^ 2 - (r1 - r3) ^ 2)
  (ht24 : t24 ^ 2 = dist c2 c4 ^ 2 - (r2 - r4) ^ 2)
  (ht12pos : 0 < t12)
  (ht23pos : 0 < t23)
  (ht34pos : 0 < t34)
  (ht41pos : 0 < t41)
  (ht13pos : 0 < t13)
  (ht24pos : 0 < t24)
  (hθ12 : θ1 < θ2)
  (hθ23 : θ2 < θ3)
  (hθ34 : θ3 < θ4)
  (hθ41 : θ4 < θ1 + 2 * Real.pi)
  (hc1 : c1 - O = dist c1 O • !₂[Real.cos θ1, Real.sin θ1])
  (hc2 : c2 - O = dist c2 O • !₂[Real.cos θ2, Real.sin θ2])
  (hc3 : c3 - O = dist c3 O • !₂[Real.cos θ3, Real.sin θ3])
  (hc4 : c4 - O = dist c4 O • !₂[Real.cos θ4, Real.sin θ4]) :
-- imply
  t12 * t34 + t23 * t41 = t13 * t24 := by
-- proof
  have hpi := Real.pi_pos
  have e1 : dist c1 O = R - r1 := by linarith
  have e2 : dist c2 O = R - r2 := by linarith
  have e3 : dist c3 O = R - r3 := by linarith
  have e4 : dist c4 O = R - r4 := by linarith
  have hd1 : (0:ℝ) < dist c1 O := by linarith
  have hd2 : (0:ℝ) < dist c2 O := by linarith
  have hd3 : (0:ℝ) < dist c3 O := by linarith
  have hd4 : (0:ℝ) < dist c4 O := by linarith
  have A1 : (0:ℝ) < R - r1 := by linarith
  have A2 : (0:ℝ) < R - r2 := by linarith
  have A3 : (0:ℝ) < R - r3 := by linarith
  have A4 : (0:ℝ) < R - r4 := by linarith
  have g12a : (0:ℝ) < θ2 - θ1 := by linarith
  have g12b : θ2 - θ1 < 2 * Real.pi := by linarith
  have g23a : (0:ℝ) < θ3 - θ2 := by linarith
  have g23b : θ3 - θ2 < 2 * Real.pi := by linarith
  have g34a : (0:ℝ) < θ4 - θ3 := by linarith
  have g34b : θ4 - θ3 < 2 * Real.pi := by linarith
  have g13a : (0:ℝ) < θ3 - θ1 := by linarith
  have g13b : θ3 - θ1 < 2 * Real.pi := by linarith
  have g24a : (0:ℝ) < θ4 - θ2 := by linarith
  have g24b : θ4 - θ2 < 2 * Real.pi := by linarith
  have g14a : (0:ℝ) < θ4 - θ1 := by linarith
  have g14b : θ4 - θ1 < 2 * Real.pi := by linarith
  have D12 : dist c1 c2 ^ 2 = dist c1 O ^ 2 + dist c2 O ^ 2
    - 2 * dist c1 O * dist c2 O * Real.cos (θ2 - θ1) :=
    dist_sq_of_angles hc1 hc2
  have D23 : dist c2 c3 ^ 2 = dist c2 O ^ 2 + dist c3 O ^ 2
    - 2 * dist c2 O * dist c3 O * Real.cos (θ3 - θ2) :=
    dist_sq_of_angles hc2 hc3
  have D34 : dist c3 c4 ^ 2 = dist c3 O ^ 2 + dist c4 O ^ 2
    - 2 * dist c3 O * dist c4 O * Real.cos (θ4 - θ3) :=
    dist_sq_of_angles hc3 hc4
  have D13 : dist c1 c3 ^ 2 = dist c1 O ^ 2 + dist c3 O ^ 2
    - 2 * dist c1 O * dist c3 O * Real.cos (θ3 - θ1) :=
    dist_sq_of_angles hc1 hc3
  have D24 : dist c2 c4 ^ 2 = dist c2 O ^ 2 + dist c4 O ^ 2
    - 2 * dist c2 O * dist c4 O * Real.cos (θ4 - θ2) :=
    dist_sq_of_angles hc2 hc4
  have D14 : dist c1 c4 ^ 2 = dist c1 O ^ 2 + dist c4 O ^ 2
    - 2 * dist c1 O * dist c4 O * Real.cos (θ4 - θ1) :=
    dist_sq_of_angles hc1 hc4
  have ht41' : t41 ^ 2 = dist c1 c4 ^ 2 - (r1 - r4) ^ 2 := by
    have h := ht41
    rw [dist_comm c4 c1] at h
    have hsq : (r4 - r1) ^ 2 = (r1 - r4) ^ 2 := by ring
    rwa [hsq] at h
  have T12 : t12 = 2 * √((R - r1) * (R - r2)) * Real.sin ((θ2 - θ1) / 2) :=
    tangent_eq_of_dist hd1 hd2 e1 e2 D12 ht12 ht12pos g12a g12b
  have T23 : t23 = 2 * √((R - r2) * (R - r3)) * Real.sin ((θ3 - θ2) / 2) :=
    tangent_eq_of_dist hd2 hd3 e2 e3 D23 ht23 ht23pos g23a g23b
  have T34 : t34 = 2 * √((R - r3) * (R - r4)) * Real.sin ((θ4 - θ3) / 2) :=
    tangent_eq_of_dist hd3 hd4 e3 e4 D34 ht34 ht34pos g34a g34b
  have T13 : t13 = 2 * √((R - r1) * (R - r3)) * Real.sin ((θ3 - θ1) / 2) :=
    tangent_eq_of_dist hd1 hd3 e1 e3 D13 ht13 ht13pos g13a g13b
  have T24 : t24 = 2 * √((R - r2) * (R - r4)) * Real.sin ((θ4 - θ2) / 2) :=
    tangent_eq_of_dist hd2 hd4 e2 e4 D24 ht24 ht24pos g24a g24b
  have T41 : t41 = 2 * √((R - r1) * (R - r4)) * Real.sin ((θ4 - θ1) / 2) :=
    tangent_eq_of_dist hd1 hd4 e1 e4 D14 ht41' ht41pos g14a g14b
  have S12 : √((R - r1) * (R - r2)) = √(R - r1) * √(R - r2) :=
    Real.sqrt_mul A1.le _
  have S23 : √((R - r2) * (R - r3)) = √(R - r2) * √(R - r3) :=
    Real.sqrt_mul A2.le _
  have S34 : √((R - r3) * (R - r4)) = √(R - r3) * √(R - r4) :=
    Real.sqrt_mul A3.le _
  have S13 : √((R - r1) * (R - r3)) = √(R - r1) * √(R - r3) :=
    Real.sqrt_mul A1.le _
  have S24 : √((R - r2) * (R - r4)) = √(R - r2) * √(R - r4) :=
    Real.sqrt_mul A2.le _
  have S41 : √((R - r1) * (R - r4)) = √(R - r1) * √(R - r4) :=
    Real.sqrt_mul A1.le _
  rw [S12] at T12
  rw [S23] at T23
  rw [S34] at T34
  rw [S41] at T41
  rw [S13] at T13
  rw [S24] at T24
  have htrig : Real.sin ((θ2 - θ1) / 2) * Real.sin ((θ4 - θ3) / 2)
    + Real.sin ((θ3 - θ2) / 2) * Real.sin ((θ4 - θ1) / 2)
    = Real.sin ((θ3 - θ1) / 2) * Real.sin ((θ4 - θ2) / 2) := by
    have h := trig_aux (a := θ2 - θ1) (b := θ3 - θ2) (c := θ4 - θ3)
    have b1 : ((θ2 - θ1) + (θ3 - θ2) + (θ4 - θ3)) / 2 = (θ4 - θ1) / 2 := by ring
    have b2 : ((θ2 - θ1) + (θ3 - θ2)) / 2 = (θ3 - θ1) / 2 := by ring
    have b3 : ((θ3 - θ2) + (θ4 - θ3)) / 2 = (θ4 - θ2) / 2 := by ring
    rwa [b1, b2, b3] at h
  rw [T12, T23, T34, T41, T13, T24]
  linear_combination 4 * √(R - r1) * √(R - r2) * √(R - r3) * √(R - r4) * htrig
set_option linter.unusedVariables false in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[casey_theorem_cyclic_order](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/CaseyTheoremCyclicOrder.lean)
-/
@[path]
lemma casey_theorem_cyclic_order
  {O c1 c2 c3 c4 : EuclideanSpace ℝ (Fin 2)}
  {R r1 r2 r3 r4 t12 t23 t34 t41 t13 t24 θ1 θ2 θ3 θ4 : ℝ}
-- given
  (hR : 0 < R)
  (hr1 : 0 < r1)
  (hr2 : 0 < r2)
  (hr3 : 0 < r3)
  (hr4 : 0 < r4)
  (hlt1 : r1 < R)
  (hlt2 : r2 < R)
  (hlt3 : r3 < R)
  (hlt4 : r4 < R)
  (hinner1 : dist c1 O + r1 = R)
  (hinner2 : dist c2 O + r2 = R)
  (hinner3 : dist c3 O + r3 = R)
  (hinner4 : dist c4 O + r4 = R)
  (hdisj12 : r1 + r2 < dist c1 c2)
  (hdisj23 : r2 + r3 < dist c2 c3)
  (hdisj34 : r3 + r4 < dist c3 c4)
  (hdisj41 : r4 + r1 < dist c4 c1)
  (hdisj13 : r1 + r3 < dist c1 c3)
  (hdisj24 : r2 + r4 < dist c2 c4)
  (ht12 : t12 ^ 2 = dist c1 c2 ^ 2 - (r1 - r2) ^ 2)
  (ht23 : t23 ^ 2 = dist c2 c3 ^ 2 - (r2 - r3) ^ 2)
  (ht34 : t34 ^ 2 = dist c3 c4 ^ 2 - (r3 - r4) ^ 2)
  (ht41 : t41 ^ 2 = dist c4 c1 ^ 2 - (r4 - r1) ^ 2)
  (ht13 : t13 ^ 2 = dist c1 c3 ^ 2 - (r1 - r3) ^ 2)
  (ht24 : t24 ^ 2 = dist c2 c4 ^ 2 - (r2 - r4) ^ 2)
  (ht12pos : 0 < t12)
  (ht23pos : 0 < t23)
  (ht34pos : 0 < t34)
  (ht41pos : 0 < t41)
  (ht13pos : 0 < t13)
  (ht24pos : 0 < t24)
  (hθ12 : θ1 < θ2)
  (hθ23 : θ2 < θ3)
  (hθ34 : θ3 < θ4)
  (hθ41 : θ4 < θ1 + 2 * Real.pi)
  (hc1 : c1 - O = dist c1 O • !₂[Real.cos θ1, Real.sin θ1])
  (hc2 : c2 - O = dist c2 O • !₂[Real.cos θ2, Real.sin θ2])
  (hc3 : c3 - O = dist c3 O • !₂[Real.cos θ3, Real.sin θ3])
  (hc4 : c4 - O = dist c4 O • !₂[Real.cos θ4, Real.sin θ4]) :
-- imply
  t12 * t34 + t23 * t41 = t13 * t24 := by
-- proof
  exact casey_theorem_cyclic_order_core hlt1 hlt2 hlt3 hlt4 hinner1 hinner2
    hinner3 hinner4 ht12 ht23 ht34 ht41 ht13 ht24 ht12pos ht23pos ht34pos ht41pos
    ht13pos ht24pos hθ12 hθ23 hθ34 hθ41 hc1 hc2 hc3 hc4

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
