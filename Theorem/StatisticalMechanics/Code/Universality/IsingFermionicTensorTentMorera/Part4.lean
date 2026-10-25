/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Def.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part2


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

theorem axisTwoEdgeStaircase_base_norm_le
    (x y mesh : Real) (width height : Nat) (hmesh : 0 ≤ mesh) :
    let p : Complex := x + y * Complex.I
    (∀ k < width,
      norm (((x + (k : Real) * mesh : Real) + y * Complex.I) - p) ≤
        (width : Real) * mesh + (height : Real) * mesh) ∧
    (∀ k < height,
      norm (((x + (width : Real) * mesh : Real) +
        (y + (k : Real) * mesh : Real) * Complex.I) - p) ≤
        (width : Real) * mesh + (height : Real) * mesh) ∧
    (∀ k < width,
      norm (((x + (width : Real) * mesh - (k : Real) * mesh : Real) +
        (y + (height : Real) * mesh : Real) * Complex.I) - p) ≤
        (width : Real) * mesh + (height : Real) * mesh) ∧
    (∀ k < height,
      norm ((x + (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
        Complex.I) - p) ≤
        (width : Real) * mesh + (height : Real) * mesh) := by
  dsimp only
  have hwidth : 0 ≤ (width : Real) * mesh := mul_nonneg (by positivity) hmesh
  have hheight : 0 ≤ (height : Real) * mesh := mul_nonneg (by positivity) hmesh
  constructor
  · intro k hk
    calc
      norm (((x + (k : Real) * mesh : Real) + y * Complex.I) -
          (x + y * Complex.I)) ≤
        |(((x + (k : Real) * mesh : Real) + y * Complex.I) -
          (x + y * Complex.I)).re| +
        |(((x + (k : Real) * mesh : Real) + y * Complex.I) -
          (x + y * Complex.I)).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = (k : Real) * mesh := by
        have hkmesh : 0 ≤ mesh * (k : Real) :=
          mul_nonneg hmesh (by positivity)
        rw [show (((x + (k : Real) * mesh : Real) + y * Complex.I) -
            (x + y * Complex.I)).re = mesh * k by simp; ring,
          show (((x + (k : Real) * mesh : Real) + y * Complex.I) -
            (x + y * Complex.I)).im = 0 by simp]
        rw [abs_of_nonneg hkmesh, abs_zero, add_zero]
        ring
      _ ≤ (width : Real) * mesh + (height : Real) * mesh := by
        have hkR : (k : Real) ≤ width := by exact_mod_cast (Nat.le_of_lt hk)
        nlinarith
  · constructor
    · intro k hk
      calc
        norm (((x + (width : Real) * mesh : Real) +
            (y + (k : Real) * mesh : Real) * Complex.I) -
            (x + y * Complex.I)) ≤
          |(((x + (width : Real) * mesh : Real) +
            (y + (k : Real) * mesh : Real) * Complex.I) -
            (x + y * Complex.I)).re| +
          |(((x + (width : Real) * mesh : Real) +
            (y + (k : Real) * mesh : Real) * Complex.I) -
            (x + y * Complex.I)).im| := Complex.norm_le_abs_re_add_abs_im _
        _ = (width : Real) * mesh + (k : Real) * mesh := by
          have hkmesh : 0 ≤ mesh * (k : Real) :=
            mul_nonneg hmesh (by positivity)
          rw [show (((x + (width : Real) * mesh : Real) +
              (y + (k : Real) * mesh : Real) * Complex.I) -
              (x + y * Complex.I)).re = width * mesh by simp,
            show (((x + (width : Real) * mesh : Real) +
              (y + (k : Real) * mesh : Real) * Complex.I) -
              (x + y * Complex.I)).im = mesh * k by simp; ring]
          rw [abs_of_nonneg hwidth, abs_of_nonneg hkmesh]
          ring
        _ ≤ (width : Real) * mesh + (height : Real) * mesh := by
          have hkR : (k : Real) ≤ height := by exact_mod_cast (Nat.le_of_lt hk)
          nlinarith
    · constructor
      · intro k hk
        calc
          norm (((x + (width : Real) * mesh - (k : Real) * mesh : Real) +
              (y + (height : Real) * mesh : Real) * Complex.I) -
              (x + y * Complex.I)) ≤
            |(((x + (width : Real) * mesh - (k : Real) * mesh : Real) +
              (y + (height : Real) * mesh : Real) * Complex.I) -
              (x + y * Complex.I)).re| +
            |(((x + (width : Real) * mesh - (k : Real) * mesh : Real) +
              (y + (height : Real) * mesh : Real) * Complex.I) -
              (x + y * Complex.I)).im| := Complex.norm_le_abs_re_add_abs_im _
          _ = ((width : Real) - k) * mesh + (height : Real) * mesh := by
            have hkR : (k : Real) ≤ width := by exact_mod_cast (Nat.le_of_lt hk)
            have hdiff : 0 ≤ (width : Real) * mesh - mesh * k := by
              nlinarith [mul_nonneg (sub_nonneg.mpr hkR) hmesh]
            rw [show (((x + (width : Real) * mesh - (k : Real) * mesh : Real) +
                (y + (height : Real) * mesh : Real) * Complex.I) -
                (x + y * Complex.I)).re = width * mesh - mesh * k by
                  simp; ring,
              show (((x + (width : Real) * mesh - (k : Real) * mesh : Real) +
                (y + (height : Real) * mesh : Real) * Complex.I) -
                (x + y * Complex.I)).im = height * mesh by simp]
            rw [abs_of_nonneg hdiff, abs_of_nonneg hheight]
            ring
          _ ≤ (width : Real) * mesh + (height : Real) * mesh := by
            have hkR : (0 : Real) ≤ k := by positivity
            nlinarith
      · intro k hk
        calc
          norm ((x +
              (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
                Complex.I) - (x + y * Complex.I)) ≤
            |((x +
              (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
                Complex.I) - (x + y * Complex.I)).re| +
            |((x +
              (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
                Complex.I) - (x + y * Complex.I)).im| :=
              Complex.norm_le_abs_re_add_abs_im _
          _ = ((height : Real) - k) * mesh := by
            have hkR : (k : Real) ≤ height := by exact_mod_cast (Nat.le_of_lt hk)
            have hdiff : 0 ≤ (height : Real) * mesh - mesh * k := by
              nlinarith [mul_nonneg (sub_nonneg.mpr hkR) hmesh]
            rw [show ((x +
                (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
                  Complex.I) - (x + y * Complex.I)).re = 0 by simp,
              show ((x +
                (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
                  Complex.I) - (x + y * Complex.I)).im =
                  height * mesh - mesh * k by simp; ring]
            rw [abs_zero, zero_add, abs_of_nonneg hdiff]
            ring
          _ ≤ (width : Real) * mesh + (height : Real) * mesh := by
            have hkR : (0 : Real) ≤ k := by positivity
            nlinarith


theorem axisMacroDirectContour_eq_wedgeContour
    (f : Complex -> Complex) (hf : Continuous f)
    (x y mesh : Real) (width height : Nat) :
    axisMacroDirectContour f x y mesh width height =
      Complex.wedgeIntegral (x + y * Complex.I)
          ((x + (width : Real) * mesh : Real) +
            (y + (height : Real) * mesh : Real) * Complex.I) f +
        Complex.wedgeIntegral
          ((x + (width : Real) * mesh : Real) +
            (y + (height : Real) * mesh : Real) * Complex.I)
          (x + y * Complex.I) f := by
  unfold axisMacroDirectContour
  rw [sum_horizontalComplexDisplacementIntegral f hf x y mesh width]
  rw [sum_verticalComplexDisplacementIntegral f hf
    (x + (width : Real) * mesh) y mesh height]
  rw [sum_horizontalComplexDisplacementIntegral f hf
    (x + (width : Real) * mesh) (y + (height : Real) * mesh)
    (-mesh) width]
  rw [sum_verticalComplexDisplacementIntegral f hf
    x (y + (height : Real) * mesh) (-mesh) height]
  convert axisRectangleDisplacementContour_eq_wedgeContour
    f x y ((width : Real) * mesh) ((height : Real) * mesh) using 1 <;>
    push_cast <;> ring


theorem norm_complexDisplacementIntegral_sub_const_mul_le
    (f : Complex -> Complex) (hf : Continuous f)
    (a v c : Complex) (epsilon : Real)
    (hosc : ∀ t ∈ Set.Icc (0 : Real) 1,
      norm (f (a + (t : Complex) * v) - c) <= epsilon) :
    norm (complexDisplacementIntegral f a v - c * v) <=
      epsilon * norm v := by
  have hpath : Continuous (fun t : Real =>
      f (a + (t : Complex) * v) * v) := by
    fun_prop
  have hconst : Continuous (fun _t : Real => c * v) := continuous_const
  have heq : complexDisplacementIntegral f a v - c * v =
      ∫ t : Real in 0..1,
        (f (a + (t : Complex) * v) - c) * v := by
    unfold complexDisplacementIntegral
    rw [show c * v = ∫ _t : Real in 0..1, c * v by simp,
      ← intervalIntegral.integral_sub (hpath.intervalIntegrable 0 1)
        (hconst.intervalIntegrable 0 1)]
    apply intervalIntegral.integral_congr
    intro t _ht
    ring
  rw [heq]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : Real)) (b := 1) (C := epsilon * norm v)
    (f := fun t : Real => (f (a + (t : Complex) * v) - c) * v)
    (fun t ht => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hosc t (Set.Ioc_subset_Icc_self ht)) (norm_nonneg v))
  simpa using hbound


theorem norm_complexDisplacementIntegral_sub_le_of_uniformNorm
    (F G : Complex -> Complex) (hF : Continuous F) (hG : Continuous G)
    (a v : Complex) (epsilon : Real)
    (herror : ∀ t ∈ Set.Icc (0 : Real) 1,
      norm (F (a + (t : Complex) * v) -
        G (a + (t : Complex) * v)) ≤ epsilon) :
    norm (complexDisplacementIntegral F a v -
      complexDisplacementIntegral G a v) ≤ epsilon * norm v := by
  have hpath : Continuous (fun t : Real => a + (t : Complex) * v) := by
    fun_prop
  have hFI : Continuous (fun t : Real =>
      F (a + (t : Complex) * v) * v) := (hF.comp hpath).mul continuous_const
  have hGI : Continuous (fun t : Real =>
      G (a + (t : Complex) * v) * v) := (hG.comp hpath).mul continuous_const
  have heq : complexDisplacementIntegral F a v -
      complexDisplacementIntegral G a v =
        complexDisplacementIntegral (fun z => F z - G z) a v := by
    unfold complexDisplacementIntegral
    rw [← intervalIntegral.integral_sub
      (hFI.intervalIntegrable 0 1) (hGI.intervalIntegrable 0 1)]
    apply intervalIntegral.integral_congr
    intro t _ht
    ring
  rw [heq]
  simpa using norm_complexDisplacementIntegral_sub_const_mul_le
    (fun z => F z - G z) (hF.sub hG) a v 0 epsilon (by
      intro t ht
      simpa using herror t ht)


theorem norm_twoStepDisplacementIntegral_sub_direct_le
    (f : Complex -> Complex) (hf : Continuous f)
    (a u v c : Complex) (epsilon : Real)
    (hu : ∀ t ∈ Set.Icc (0 : Real) 1,
      norm (f (a + (t : Complex) * u) - c) <= epsilon)
    (hv : ∀ t ∈ Set.Icc (0 : Real) 1,
      norm (f (a + u + (t : Complex) * v) - c) <= epsilon)
    (hdirect : ∀ t ∈ Set.Icc (0 : Real) 1,
      norm (f (a + (t : Complex) * (u + v)) - c) <= epsilon) :
    norm (complexDisplacementIntegral f a u +
        complexDisplacementIntegral f (a + u) v -
        complexDisplacementIntegral f a (u + v)) <=
      epsilon * (norm u + norm v + norm (u + v)) := by
  have hU := norm_complexDisplacementIntegral_sub_const_mul_le
    f hf a u c epsilon hu
  have hV := norm_complexDisplacementIntegral_sub_const_mul_le
    f hf (a + u) v c epsilon hv
  have hD := norm_complexDisplacementIntegral_sub_const_mul_le
    f hf a (u + v) c epsilon hdirect
  calc
    norm (complexDisplacementIntegral f a u +
        complexDisplacementIntegral f (a + u) v -
        complexDisplacementIntegral f a (u + v)) =
      norm ((complexDisplacementIntegral f a u - c * u) +
        (complexDisplacementIntegral f (a + u) v - c * v) -
        (complexDisplacementIntegral f a (u + v) - c * (u + v))) := by
          congr 1
          ring
    _ <= norm (complexDisplacementIntegral f a u - c * u) +
        norm (complexDisplacementIntegral f (a + u) v - c * v) +
        norm (complexDisplacementIntegral f a (u + v) - c * (u + v)) := by
      exact (norm_sub_le _ _).trans
        (add_le_add (norm_add_le _ _) (le_refl _))
    _ <= epsilon * norm u + epsilon * norm v + epsilon * norm (u + v) :=
      add_le_add (add_le_add hU hV) hD
    _ = epsilon * (norm u + norm v + norm (u + v)) := by ring


theorem norm_twoStepDisplacementIntegral_sub_direct_le_of_ball
    (f : Complex -> Complex) (hf : Continuous f)
    (a u v : Complex) (epsilon radius : Real)
    (huNorm : norm u ≤ radius) (hvNorm : norm v ≤ radius)
    (hosc : ∀ q, norm (q - a) ≤ 2 * radius ->
      norm (f q - f a) ≤ epsilon) :
    norm (complexDisplacementIntegral f a u +
        complexDisplacementIntegral f (a + u) v -
        complexDisplacementIntegral f a (u + v)) ≤
      epsilon * (norm u + norm v + norm (u + v)) := by
  apply norm_twoStepDisplacementIntegral_sub_direct_le
    f hf a u v (f a) epsilon
  · intro t ht
    apply hosc
    rw [show a + (t : Complex) * u - a = (t : Complex) * u by ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have htNorm : |t| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    calc
      |t| * norm u ≤ 1 * radius :=
        mul_le_mul htNorm huNorm (norm_nonneg u) (by
          nlinarith [norm_nonneg u])
      _ ≤ 2 * radius := by nlinarith [norm_nonneg u]
  · intro t ht
    apply hosc
    rw [show a + u + (t : Complex) * v - a = u + (t : Complex) * v by ring]
    calc
      norm (u + (t : Complex) * v) ≤ norm u + norm ((t : Complex) * v) :=
        norm_add_le _ _
      _ = norm u + |t| * norm v := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 * radius := by
        have htNorm : |t| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [ht.1, ht.2]
        have hmul : |t| * norm v ≤ radius := by
          calc
            |t| * norm v ≤ 1 * radius :=
              mul_le_mul htNorm hvNorm (norm_nonneg v) (by
                nlinarith [norm_nonneg v])
            _ = radius := one_mul radius
        linarith
  · intro t ht
    apply hosc
    rw [show a + (t : Complex) * (u + v) - a =
      (t : Complex) * (u + v) by ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have htNorm : |t| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have huv := norm_add_le u v
    have hsum : norm (u + v) ≤ 2 * radius := by linarith
    calc
      |t| * norm (u + v) ≤ 1 * (2 * radius) :=
        mul_le_mul htNorm hsum (norm_nonneg (u + v)) (by
          nlinarith [norm_nonneg u])
      _ = 2 * radius := one_mul _


theorem norm_sum_twoStepDisplacementIntegral_sub_direct_le
    (f : Complex -> Complex) (hf : Continuous f)
    (N : Nat) (a u v c : Nat -> Complex) (epsilon : Nat -> Real)
    (hu : ∀ k < N, ∀ t ∈ Set.Icc (0 : Real) 1,
      norm (f (a k + (t : Complex) * u k) - c k) <= epsilon k)
    (hv : ∀ k < N, ∀ t ∈ Set.Icc (0 : Real) 1,
      norm (f (a k + u k + (t : Complex) * v k) - c k) <= epsilon k)
    (hdirect : ∀ k < N, ∀ t ∈ Set.Icc (0 : Real) 1,
      norm (f (a k + (t : Complex) * (u k + v k)) - c k) <=
        epsilon k) :
    norm (∑ k ∈ Finset.range N,
      (complexDisplacementIntegral f (a k) (u k) +
        complexDisplacementIntegral f (a k + u k) (v k) -
        complexDisplacementIntegral f (a k) (u k + v k))) <=
      ∑ k ∈ Finset.range N,
        epsilon k * (norm (u k) + norm (v k) + norm (u k + v k)) := by
  calc
    norm (∑ k ∈ Finset.range N,
        (complexDisplacementIntegral f (a k) (u k) +
          complexDisplacementIntegral f (a k + u k) (v k) -
          complexDisplacementIntegral f (a k) (u k + v k))) <=
        ∑ k ∈ Finset.range N,
          norm (complexDisplacementIntegral f (a k) (u k) +
            complexDisplacementIntegral f (a k + u k) (v k) -
            complexDisplacementIntegral f (a k) (u k + v k)) :=
      norm_sum_le _ _
    _ <= ∑ k ∈ Finset.range N,
        epsilon k * (norm (u k) + norm (v k) + norm (u k + v k)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact norm_twoStepDisplacementIntegral_sub_direct_le
        f hf (a k) (u k) (v k) (c k) (epsilon k)
        (hu k (Finset.mem_range.mp hk))
        (hv k (Finset.mem_range.mp hk))
        (hdirect k (Finset.mem_range.mp hk))


theorem norm_sum_twoEdgePath_sub_direct_le_of_ball
    (f : Complex -> Complex) (hf : Continuous f)
    (N : Nat) (a : Nat -> Complex) (u v : Complex)
    (epsilon radius : Real)
    (huNorm : norm u ≤ radius) (hvNorm : norm v ≤ radius)
    (hosc : ∀ k < N, ∀ q, norm (q - a k) ≤ 2 * radius ->
      norm (f q - f (a k)) ≤ epsilon) :
    norm ((∑ k ∈ Finset.range N,
        (complexDisplacementIntegral f (a k) u +
          complexDisplacementIntegral f (a k + u) v)) -
      ∑ k ∈ Finset.range N,
        complexDisplacementIntegral f (a k) (u + v)) ≤
      ∑ k ∈ Finset.range N,
        epsilon * (norm u + norm v + norm (u + v)) := by
  rw [← Finset.sum_sub_distrib]
  calc
    norm (∑ k ∈ Finset.range N,
        ((complexDisplacementIntegral f (a k) u +
          complexDisplacementIntegral f (a k + u) v) -
        complexDisplacementIntegral f (a k) (u + v))) ≤
      ∑ k ∈ Finset.range N,
        norm ((complexDisplacementIntegral f (a k) u +
          complexDisplacementIntegral f (a k + u) v) -
        complexDisplacementIntegral f (a k) (u + v)) := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N,
        epsilon * (norm u + norm v + norm (u + v)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply norm_twoStepDisplacementIntegral_sub_direct_le_of_ball
        f hf (a k) u v epsilon radius huNorm hvNorm
      exact hosc k (Finset.mem_range.mp hk)


theorem norm_sum_twoEdgePath_sub_le_of_uniformNorm
    (F G : Complex -> Complex) (hF : Continuous F) (hG : Continuous G)
    (N : Nat) (a : Nat -> Complex) (u v : Complex) (epsilon : Real)
    (herror : ∀ k < N, ∀ q,
      (∃ t ∈ Set.Icc (0 : Real) 1, q = a k + (t : Complex) * u) ∨
      (∃ t ∈ Set.Icc (0 : Real) 1,
        q = a k + u + (t : Complex) * v) ->
      norm (F q - G q) ≤ epsilon) :
    norm ((∑ k ∈ Finset.range N,
        (complexDisplacementIntegral F (a k) u +
          complexDisplacementIntegral F (a k + u) v)) -
      ∑ k ∈ Finset.range N,
        (complexDisplacementIntegral G (a k) u +
          complexDisplacementIntegral G (a k + u) v)) ≤
      ∑ k ∈ Finset.range N, epsilon * (norm u + norm v) := by
  rw [← Finset.sum_sub_distrib]
  calc
    norm (∑ k ∈ Finset.range N,
        ((complexDisplacementIntegral F (a k) u +
          complexDisplacementIntegral F (a k + u) v) -
        (complexDisplacementIntegral G (a k) u +
          complexDisplacementIntegral G (a k + u) v))) ≤
      ∑ k ∈ Finset.range N,
        norm ((complexDisplacementIntegral F (a k) u +
          complexDisplacementIntegral F (a k + u) v) -
        (complexDisplacementIntegral G (a k) u +
          complexDisplacementIntegral G (a k + u) v)) := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N, epsilon * (norm u + norm v) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hu := norm_complexDisplacementIntegral_sub_le_of_uniformNorm
        F G hF hG (a k) u epsilon (by
          intro t ht
          exact herror k hk' _ (Or.inl ⟨t, ht, rfl⟩))
      have hv := norm_complexDisplacementIntegral_sub_le_of_uniformNorm
        F G hF hG (a k + u) v epsilon (by
          intro t ht
          exact herror k hk' _ (Or.inr ⟨t, ht, rfl⟩))
      calc
        norm ((complexDisplacementIntegral F (a k) u +
            complexDisplacementIntegral F (a k + u) v) -
          (complexDisplacementIntegral G (a k) u +
            complexDisplacementIntegral G (a k + u) v)) =
          norm ((complexDisplacementIntegral F (a k) u -
              complexDisplacementIntegral G (a k) u) +
            (complexDisplacementIntegral F (a k + u) v -
              complexDisplacementIntegral G (a k + u) v)) := by
                congr 1
                ring
        _ ≤ norm (complexDisplacementIntegral F (a k) u -
              complexDisplacementIntegral G (a k) u) +
            norm (complexDisplacementIntegral F (a k + u) v -
              complexDisplacementIntegral G (a k + u) v) := norm_add_le _ _
        _ ≤ epsilon * norm u + epsilon * norm v := add_le_add hu hv
        _ = epsilon * (norm u + norm v) := by ring


theorem norm_axisTwoEdgeStaircasePathIntegral_sub_le_of_uniformNorm
    (F G : Complex -> Complex) (hF : Continuous F) (hG : Continuous G)
    (x y mesh : Real) (width height : Nat) (epsilon : Real)
    (hmesh : 0 < mesh) (herror : ∀ q, norm (F q - G q) ≤ epsilon) :
    norm (axisTwoEdgeStaircasePathIntegral F x y mesh width height -
      axisTwoEdgeStaircasePathIntegral G x y mesh width height) ≤
        4 * epsilon * mesh * (width + height) := by
  let u : Complex := (mesh : Complex) / 2 * (1 - Complex.I)
  let v : Complex := (mesh : Complex) / 2 * (1 + Complex.I)
  let ab : Nat -> Complex := fun k =>
    (x + (k : Real) * mesh : Real) + y * Complex.I
  let ar : Nat -> Complex := fun k =>
    (x + (width : Real) * mesh : Real) +
      (y + (k : Real) * mesh : Real) * Complex.I
  let atop : Nat -> Complex := fun k =>
    (x + (width : Real) * mesh - (k : Real) * mesh : Real) +
      (y + (height : Real) * mesh : Real) * Complex.I
  let al : Nat -> Complex := fun k =>
    x + (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
      Complex.I
  have hepsilon : 0 ≤ epsilon := (norm_nonneg (F 0 - G 0)).trans (herror 0)
  have huNorm : norm u ≤ mesh := by
    dsimp only [u]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hmesh]
    norm_num
    have h := norm_sub_le (1 : Complex) Complex.I
    rw [norm_one, Complex.norm_I] at h
    nlinarith
  have hvNorm : norm v ≤ mesh := by
    dsimp only [v]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hmesh]
    norm_num
    have h := norm_add_le (1 : Complex) Complex.I
    rw [norm_one, Complex.norm_I] at h
    nlinarith
  have sideBound (N : Nat) (a : Nat -> Complex) (du dv : Complex)
      (hdu : norm du ≤ mesh) (hdv : norm dv ≤ mesh) :
      norm ((∑ k ∈ Finset.range N,
          (complexDisplacementIntegral F (a k) du +
            complexDisplacementIntegral F (a k + du) dv)) -
        ∑ k ∈ Finset.range N,
          (complexDisplacementIntegral G (a k) du +
            complexDisplacementIntegral G (a k + du) dv)) ≤
        2 * epsilon * mesh * N := by
    calc
      _ ≤ ∑ k ∈ Finset.range N,
          epsilon * (norm du + norm dv) :=
        norm_sum_twoEdgePath_sub_le_of_uniformNorm
          F G hF hG N a du dv epsilon (by
            intro k hk q _hq
            exact herror q)
      _ ≤ ∑ _k ∈ Finset.range N, 2 * epsilon * mesh := by
        apply Finset.sum_le_sum
        intro k hk
        nlinarith
      _ = 2 * epsilon * mesh * N := by
        simp
        ring
  have hb := sideBound width ab u v huNorm hvNorm
  have hr := sideBound height ar v (-u) hvNorm (by simpa using huNorm)
  have ht := sideBound width atop (-u) (-v)
    (by simpa using huNorm) (by simpa using hvNorm)
  have hl := sideBound height al (-v) u (by simpa using hvNorm) huNorm
  have ht' :
      norm ((∑ k ∈ Finset.range width,
          (complexDisplacementIntegral F (atop k) (-u) +
            complexDisplacementIntegral F (atop k - u) (-v))) -
        ∑ k ∈ Finset.range width,
          (complexDisplacementIntegral G (atop k) (-u) +
            complexDisplacementIntegral G (atop k - u) (-v))) ≤
        2 * epsilon * mesh * width := by
    simpa [sub_eq_add_neg] using ht
  have hl' :
      norm ((∑ k ∈ Finset.range height,
          (complexDisplacementIntegral F (al k) (-v) +
            complexDisplacementIntegral F (al k - v) u)) -
        ∑ k ∈ Finset.range height,
          (complexDisplacementIntegral G (al k) (-v) +
            complexDisplacementIntegral G (al k - v) u)) ≤
        2 * epsilon * mesh * height := by
    simpa [sub_eq_add_neg] using hl
  have hdecomp :
      axisTwoEdgeStaircasePathIntegral F x y mesh width height -
          axisTwoEdgeStaircasePathIntegral G x y mesh width height =
        ((∑ k ∈ Finset.range width,
            (complexDisplacementIntegral F (ab k) u +
              complexDisplacementIntegral F (ab k + u) v)) -
          ∑ k ∈ Finset.range width,
            (complexDisplacementIntegral G (ab k) u +
              complexDisplacementIntegral G (ab k + u) v)) +
        ((∑ k ∈ Finset.range height,
            (complexDisplacementIntegral F (ar k) v +
              complexDisplacementIntegral F (ar k + v) (-u))) -
          ∑ k ∈ Finset.range height,
            (complexDisplacementIntegral G (ar k) v +
              complexDisplacementIntegral G (ar k + v) (-u))) +
        ((∑ k ∈ Finset.range width,
            (complexDisplacementIntegral F (atop k) (-u) +
              complexDisplacementIntegral F (atop k - u) (-v))) -
          ∑ k ∈ Finset.range width,
            (complexDisplacementIntegral G (atop k) (-u) +
              complexDisplacementIntegral G (atop k - u) (-v))) +
        ((∑ k ∈ Finset.range height,
            (complexDisplacementIntegral F (al k) (-v) +
              complexDisplacementIntegral F (al k - v) u)) -
          ∑ k ∈ Finset.range height,
            (complexDisplacementIntegral G (al k) (-v) +
              complexDisplacementIntegral G (al k - v) u)) := by
    unfold axisTwoEdgeStaircasePathIntegral
    dsimp only [u, v, ab, ar, atop, al]
    ring
  rw [hdecomp]
  calc
    norm (_ + _ + _ + _) ≤ norm (_ + _ + _) + norm _ := norm_add_le _ _
    _ ≤ (norm (_ + _) + norm _) + norm _ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ((norm _ + norm _) + norm _) + norm _ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (2 * epsilon * mesh * width +
          2 * epsilon * mesh * height) +
        2 * epsilon * mesh * width +
          2 * epsilon * mesh * height := by
      exact add_le_add (add_le_add (add_le_add hb hr) ht') hl'
    _ = 4 * epsilon * mesh * (width + height) := by
      push_cast
      ring


theorem VanishingRectangleContourError.isConservativeOn_subsequentialLimit
    {F : Nat -> Complex -> Complex}
    (H : VanishingRectangleContourError F)
    (hF : forall n, Continuous (F n))
    {sigma : Nat -> Nat} (hsigma : Tendsto sigma atTop atTop)
    {f : Complex -> Complex}
    (hlimit : TendstoLocallyUniformlyOn (fun n => F (sigma n)) f atTop
      Set.univ) :
    Complex.IsConservativeOn f Set.univ := by
  have hf : Continuous f := continuousOn_univ.mp
    (hlimit.continuousOn (Filter.Frequently.of_forall
      (fun n => (hF (sigma n)).continuousOn)))
  intro z w _hrect
  have hcontourLimit : Tendsto
      (fun n => Complex.wedgeIntegral z w (F (sigma n)) +
        Complex.wedgeIntegral w z (F (sigma n))) atTop
      (nhds (Complex.wedgeIntegral z w f +
        Complex.wedgeIntegral w z f)) :=
    (complex_wedgeIntegral_tendsto_of_locallyUniform
      (fun n => hF (sigma n)) hlimit z w).add
      (complex_wedgeIntegral_tendsto_of_locallyUniform
        (fun n => hF (sigma n)) hlimit w z)
  have hzero := H.contour_tendsto_zero_comp hsigma z w
  have heq : Complex.wedgeIntegral z w f +
      Complex.wedgeIntegral w z f = 0 :=
    tendsto_nhds_unique hcontourLimit hzero
  exact eq_neg_of_add_eq_zero_left heq


theorem isingCellCRAt_conj_radialGridPosition
    (mesh : Real) (i j : Nat) :
    IsingCellCRAt
      (fun a b => (starRingEnd Complex) (isingRadialGridPosition mesh a b))
      i j := by
  unfold IsingCellCRAt isingRadialGridPosition
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;>
    ring


theorem isingCellCRAt_radialGridPosition_iff
    (mesh : Real) (i j : Nat) :
    IsingCellCRAt (fun a b => isingRadialGridPosition mesh a b) i j <->
      mesh = 0 := by
  constructor
  · intro h
    unfold IsingCellCRAt isingRadialGridPosition at h
    have him := congrArg Complex.im h
    simp [Complex.mul_re, Complex.mul_im] at him
    linarith
  · rintro rfl
    simp [IsingCellCRAt, isingRadialGridPosition]


end
end StatMech.Universality
