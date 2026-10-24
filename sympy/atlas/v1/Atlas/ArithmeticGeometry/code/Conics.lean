/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Conics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.HasseMinkowski
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HasseMinkowski
import Mathlib

/-- In a field $K$ with $\operatorname{char}(K) \neq 2$, the element $2$ is invertible. -/
@[reducible]
def invertibleTwoOfRingCharNeTwo (hK : ringChar K ≠ 2) : Invertible (2 : K) := by
  apply invertibleOfRingCharNotDvd
  intro (h : ringChar K ∣ 2)
  apply hK
  have hle : ringChar K ≤ 2 := Nat.le_of_dvd (by omega) h
  have hne0 : ringChar K ≠ 0 := by
    intro h0; rw [h0] at h; exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) h
  have hne1 : ringChar K ≠ 1 := by
    intro h1; exact not_subsingleton K (ringChar.ringChar_eq_one.mp h1)
  omega

variable [Invertible (2 : K)]

/-- A quadratic form $Q$ is geometrically irreducible if its associated bilinear form is left-nondegenerate (separating). This makes the associated conic absolutely irreducible. -/
def QuadraticForm.IsGeometricallyIrreducible
    {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : Prop :=
  (associated (R := K) Q).SeparatingLeft

/-- The quadratic form $ax^2 + by^2 + cz^2 + dxy + exz + fyz$ on $K^3$, encoded as the matrix $\begin{pmatrix} a & d/2 & e/2 \\ d/2 & b & f/2 \\ e/2 & f/2 & c \end{pmatrix}$. -/
def generalConicQuadForm (a b c d e f : K) : QuadraticForm K (Fin 3 → K) :=
  Matrix.toQuadraticMap' !![a, d/2, e/2; d/2, b, f/2; e/2, f/2, c]


/-- Alias for `generalConicQuadForm`: the general ternary quadratic form $ax^2 + by^2 + cz^2 + dxy + exz + fyz$. -/
def generalConicForm (a b c d e f : K) : QuadraticForm K (Fin 3 → K) :=
  Matrix.toQuadraticMap' !![a, d/2, e/2; d/2, b, f/2; e/2, f/2, c]


section Theorem23

variable {K : Type*} [Field K]

/-- Stereographic projection (forward map): given a base point $(x_0, y_0, z_0)$ on the diagonal conic $aX^2 + bY^2 + cZ^2 = 0$, this maps $(U, V) \in \mathbb{P}^1$ to a point on the conic via a quadratic formula. -/
def stereoForward (a b x₀ y₀ z₀ U V : K) : Fin 3 → K := fun i =>
  match i with
  | 0 => a * x₀ * U ^ 2 + 2 * b * y₀ * U * V - b * x₀ * V ^ 2
  | 1 => -(a * y₀) * U ^ 2 + 2 * a * x₀ * U * V + b * y₀ * V ^ 2
  | 2 => -(a * z₀) * U ^ 2 - b * z₀ * V ^ 2

/-- Stereographic projection (backward map): given a point $v = (X, Y, Z)$ on the conic, projects from the base point $(x_0, y_0, z_0)$ to a point in $\mathbb{P}^1$. -/
def stereoBackward (x₀ y₀ z₀ : K) (v : Fin 3 → K) : Fin 2 → K := fun i =>
  match i with
  | 0 => v 0 * z₀ - x₀ * v 2
  | 1 => v 1 * z₀ - y₀ * v 2

/-- Quadratic homogeneity: scaling the input $(U, V)$ by $t$ scales the stereographic forward map by $t^2$ (so it descends to projective space). -/
theorem stereoForward_smul (a b x₀ y₀ z₀ t U V : K) (i : Fin 3) :
    stereoForward a b x₀ y₀ z₀ (t * U) (t * V) i =
    t ^ 2 * stereoForward a b x₀ y₀ z₀ U V i := by
  fin_cases i <;> simp only [stereoForward] <;> ring


/-- The bilinear pairing $\langle (x_0, y_0, z_0), (x, y, z) \rangle = a x_0 x + b y_0 y + c z_0 z$ associated to the diagonal conic; encodes the polarization of the quadratic form. -/
def bilinScalar (a b c x₀ y₀ z₀ x y z : K) : K :=
  a * x₀ * x + b * y₀ * y + c * z₀ * z

/-- A function $v : \mathrm{Fin}\,2 \to K$ is nonzero iff not both coordinates $v(0), v(1)$ are zero. -/
lemma fin2_ne_zero_iff {K : Type*} [Field K] (v : Fin 2 → K) :
    v ≠ 0 ↔ ¬(v 0 = 0 ∧ v 1 = 0) := by
  constructor
  · intro hv ⟨h0, h1⟩; apply hv; ext i; fin_cases i <;> assumption
  · intro hv h; apply hv; exact ⟨by rw [h]; rfl, by rw [h]; rfl⟩


/-- The stereographic forward map sends any nonzero $(U, V)$ to a nonzero point of $K^3$. This is needed to descend the map to projective space. -/
theorem stereoForward_ne_zero (a b c x₀ y₀ z₀ U V : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0)
    (h2ne : (2 : K) ≠ 0)
    (hpt : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = 0)
    (hUV : ¬(U = 0 ∧ V = 0)) :
    stereoForward a b x₀ y₀ z₀ U V ≠ 0 := by
  intro h
  have h0 : stereoForward a b x₀ y₀ z₀ U V 0 = 0 := by rw [h]; rfl
  have h2 : stereoForward a b x₀ y₀ z₀ U V 2 = 0 := by rw [h]; rfl
  simp only [stereoForward] at h0 h2
  have haUbV : a * U ^ 2 + b * V ^ 2 = 0 := by
    have : z₀ * (a * U ^ 2 + b * V ^ 2) = 0 := by linear_combination -h2
    exact (mul_eq_zero.mp this).resolve_left hz₀
  have key : 2 * b * V * (y₀ * U - x₀ * V) = 0 := by linear_combination h0 - x₀ * haUbV
  have h2bne : (2 : K) * b ≠ 0 := mul_ne_zero h2ne hb
  have hsum_ne : a * x₀ ^ 2 + b * y₀ ^ 2 ≠ 0 := by
    intro hsum
    have : c * z₀ ^ 2 = 0 := by linear_combination hpt - hsum
    exact mul_ne_zero hc (pow_ne_zero _ hz₀) this
  rcases mul_eq_zero.mp key with h2bV | hyx
  · rcases mul_eq_zero.mp h2bV with h2b_bad | hV
    · exact absurd h2b_bad h2bne
    · have hU : U = 0 := by
        have : a * U ^ 2 = 0 := by
          rw [hV, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero] at haUbV; exact haUbV
        exact (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp ((mul_eq_zero.mp this).resolve_left ha)
      exact hUV ⟨hU, hV⟩
  · have hyx_eq : y₀ * U = x₀ * V := sub_eq_zero.mp hyx
    have hkey : U ^ 2 * (a * x₀ ^ 2 + b * y₀ ^ 2) = 0 := by
      have : U ^ 2 * (a * x₀ ^ 2 + b * y₀ ^ 2) =
        x₀ ^ 2 * (a * U ^ 2 + b * V ^ 2) +
          b * (y₀ * U - x₀ * V) * (y₀ * U + x₀ * V) := by ring
      rw [this, haUbV, show y₀ * U - x₀ * V = 0 from sub_eq_zero.mpr hyx_eq]; ring
    rcases mul_eq_zero.mp hkey with hU2 | hsum
    · have hU : U = 0 := (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp hU2
      have hV : V = 0 := by
        rw [hU, mul_zero] at hyx_eq
        rcases mul_eq_zero.mp hyx_eq.symm with hx | hV
        · have : b * V ^ 2 = 0 := by
            rw [hU, zero_pow (by omega : 2 ≠ 0), mul_zero, zero_add] at haUbV; exact haUbV
          exact (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp ((mul_eq_zero.mp this).resolve_left hb)
        · exact hV
      exact hUV ⟨hU, hV⟩
    · exact absurd hsum hsum_ne

/-- The diagonal conic as a subset of $\mathbb{P}^2(K)$: the projective points $[x : y : z]$ satisfying $ax^2 + by^2 + cz^2 = 0$. -/
def DiagConicSet (K : Type*) [Field K] (a b c : K) :
    Set (Projectivization K (Fin 3 → K)) :=
  { P | a * (P.rep 0) ^ 2 + b * (P.rep 1) ^ 2 + c * (P.rep 2) ^ 2 = 0 }

/-- The projectivized stereographic forward map $\mathbb{P}^1(K) \to \mathbb{P}^2(K)$ induced by `stereoForward`, using the quadratic homogeneity to descend to projective space. -/
noncomputable def stereoForwardProj (a b c x₀ y₀ z₀ : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hz₀ : z₀ ≠ 0) (h2ne : (2 : K) ≠ 0)
    (hpt : a * x₀ ^ 2 + b * y₀ ^ 2 + c * z₀ ^ 2 = 0) :
    Projectivization K (Fin 2 → K) → Projectivization K (Fin 3 → K) :=
  Projectivization.lift
    (fun v => Projectivization.mk K
      (stereoForward a b x₀ y₀ z₀ (v.val 0) (v.val 1))
      (stereoForward_ne_zero a b c x₀ y₀ z₀ _ _ ha hb hc hz₀ h2ne hpt
        ((fin2_ne_zero_iff _).mp v.prop)))
    (by
      intro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ t ht
      have hw : w₁ = t • w₂ := ht
      have h0 : w₁ 0 = t * w₂ 0 := by rw [hw]; simp [Pi.smul_apply, smul_eq_mul]
      have h1 : w₁ 1 = t * w₂ 1 := by rw [hw]; simp [Pi.smul_apply, smul_eq_mul]
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨t ^ 2, funext fun i => by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [h0, h1]
        exact (stereoForward_smul a b x₀ y₀ z₀ t (w₂ 0) (w₂ 1) i).symm⟩)
