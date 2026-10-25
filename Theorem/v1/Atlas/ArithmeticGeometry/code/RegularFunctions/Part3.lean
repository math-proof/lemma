/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Opposites
import Def.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part5
open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section Theorem158

variable {k : Type*} [Field k]

open MvPolynomial

/-- Independence of representation for `evalRatFunAt`: any representation $r = f/g$ with
$g(P) \neq 0$ gives the same value $f(P)/g(P)$ for the evaluation of $r$ at $P$. -/
lemma evalRatFunAt_eq {k : Type*} [Field k] {n : ℕ}
    {X : Set (Fin n → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (r : FractionRing (AffineCoordinateRingBar X))
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsRegularAt r P hP)
    (g f_val : AffineCoordinateRingBar X)
    (hg_ne : evalBarAtPoint k X P hP g ≠ 0)
    (hgr : algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X)) g * r =
      algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X)) f_val) :
    evalRatFunAt r P hP hreg = evalBarAtPoint k X P hP f_val /
      evalBarAtPoint k X P hP g := by
  show evalBarAtPoint k X P hP hreg.choose_spec.2.choose /
    evalBarAtPoint k X P hP hreg.choose =
    evalBarAtPoint k X P hP f_val / evalBarAtPoint k X P hP g
  set g₀ := hreg.choose with hg₀_def
  set f₀ := hreg.choose_spec.2.choose with hf₀_def
  have hg₀_ne : evalBarAtPoint k X P hP g₀ ≠ 0 := hreg.choose_spec.1
  have hf₀_eq : (algebraMap (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))) f₀ =
    (algebraMap (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))) g₀ * r :=
    hreg.choose_spec.2.choose_spec
  have h_cross : f₀ * g = g₀ * f_val := by
    apply IsFractionRing.injective (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))
    simp only [map_mul]
    calc _ = (algebraMap _ _ g₀ * r) * algebraMap _ _ g := by rw [hf₀_eq]
      _ = algebraMap _ _ g₀ * (algebraMap _ _ g * r) := by ring
      _ = algebraMap _ _ g₀ * algebraMap _ _ f_val := by rw [hgr]
  have h_eval_cross : evalBarAtPoint k X P hP f₀ * evalBarAtPoint k X P hP g =
      evalBarAtPoint k X P hP g₀ * evalBarAtPoint k X P hP f_val := by
    rw [← map_mul, ← map_mul, h_cross]
  rw [div_eq_div_iff hg₀_ne hg_ne]
  rw [mul_comm (evalBarAtPoint k X P hP f_val)]
  exact h_eval_cross

/-- Characterizing property of the induced rational map: evaluating a polynomial $f$
in the target coordinates at the image point $\theta(P)$ equals the value of $\theta(f)$
at the point $P$. This is the key step proving compatibility of $\theta$ with point
evaluation. -/
theorem characterizing_property
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (hθ : IsKbarFunctionFieldHom θ)
    (f : MvPolynomial (Fin n_cod) (AlgebraicClosure k))
    (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsTupleRegularAt (functionFieldMorphismComponents θ) P hP)
    (hreg_θf : IsRegularAt
      (θ ((algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)))
      P hP) :
    MvPolynomial.eval (evalTupleAt (functionFieldMorphismComponents θ) P hP hreg) f =
    evalRatFunAt
      (θ ((algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)))
      P hP hreg_θf := by

  obtain ⟨g₀, f₀, hg₀_ne, hf₀_eq, hf₀_eval⟩ :=
    eval₂_clearing_denominators θ hθ P hP hreg f


  have h_eval₂ := theta_algebraMap_mk_eq_eval₂ θ hθ f


  have hgr : (algebraMap (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))) g₀ *
    θ ((algebraMap (AffineCoordinateRingBar Y)
      (FractionRing (AffineCoordinateRingBar Y)))
      (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)) =
    (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) f₀ := by
    rw [h_eval₂]; exact hf₀_eq.symm

  rw [evalRatFunAt_eq _ P hP hreg_θf g₀ f₀ hg₀_ne hgr]

  rw [eq_div_iff hg₀_ne]

  exact hf₀_eval

/-- Any ring homomorphism $\theta : \bar k(Y) \to \bar k(X)$ kills the ideal $\mathcal{I}(Y)$:
the polynomial $f \in \mathcal{I}(Y)$ becomes zero in $\bar k[Y]$ (since the quotient is
the coordinate ring), so its image in $\bar k(Y)$ is zero, hence $\theta(f) = 0$. -/
lemma θ_kills_ideal {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (f : MvPolynomial (Fin n_cod) (AlgebraicClosure k))
    (hf : f ∈ idealOfAlgebraicSet Y) :
    θ ((algebraMap (AffineCoordinateRingBar Y)
      (FractionRing (AffineCoordinateRingBar Y)))
      (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)) = 0 := by
  have hmk : (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f : AffineCoordinateRingBar Y) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hf
  have : (Ideal.Quotient.mk (idealOfAlgebraicSet Y)) f = (0 : AffineCoordinateRingBar Y) :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hf
  rw [this, map_zero, map_zero]

/-- The zero rational function is regular at every point: with denominator $g = 1$ (which
satisfies $g(P) = 1 \neq 0$), we have $g \cdot 0 = 0$ in the image of $\bar k[X]$. -/
lemma isRegularAt_zero {m : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (P : Fin m → AlgebraicClosure k) (hP : P ∈ X) :
    IsRegularAt (0 : FractionRing (AffineCoordinateRingBar X)) P hP := by
  refine ⟨1, ?_, ?_⟩
  · simp [evalBarAtPoint, ne_eq, one_ne_zero, not_false_eq_true]
  · simp only [map_one, one_mul]
    exact ⟨0, by simp⟩

/-- The value of the zero rational function at any point is zero. -/
lemma evalRatFunAt_zero {m : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsRegularAt (0 : FractionRing (AffineCoordinateRingBar X)) P hP) :
    evalRatFunAt 0 P hP hreg = 0 := by


  unfold evalRatFunAt
  have hmem := hreg.choose_spec.2
  have h_eq : (algebraMap (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))) hmem.choose =
    (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) hreg.choose * 0 := hmem.choose_spec
  have h_zero : hmem.choose = 0 := by
    have : (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) hmem.choose = 0 := by
      rw [h_eq]; ring
    rwa [map_eq_zero_iff _ (IsFractionRing.injective _ _)] at this
  simp [evalBarAtPoint]

/-- The image of the rational map induced by a $\bar k$-algebra homomorphism $\theta$
lands in $Y$: at any point $P$ where the components are regular, the evaluated tuple
$(\theta(Y_1)(P), \dots, \theta(Y_{n_\mathrm{cod}})(P))$ satisfies every equation of
$\mathcal{I}(Y)$, hence lies in $Y$. -/
theorem functionFieldMorphism_image_mem {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (hθ : IsKbarFunctionFieldHom θ)
    (hY : IsAlgebraicSubset k n_cod Y)
    (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsTupleRegularAt (functionFieldMorphismComponents θ) P hP) :
    evalTupleAt (functionFieldMorphismComponents θ) P hP hreg ∈ Y := by


  suffices h : evalTupleAt (functionFieldMorphismComponents θ) P hP hreg ∈
      AlgebraicSet k n_cod ((idealOfAlgebraicSet Y) : Set _) by
    rwa [algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hY] at h
  intro f hf


  have hθf_zero := θ_kills_ideal θ f hf
  have hreg_0 : IsRegularAt
      (θ ((algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)))
      P hP := by
    rw [hθf_zero]; exact isRegularAt_zero P hP
  rw [characterizing_property θ hθ f P hP hreg hreg_0]


  have hreg_0' : IsRegularAt (0 : FractionRing (AffineCoordinateRingBar X)) P hP :=
    hθf_zero ▸ hreg_0
  have : evalRatFunAt (θ ((algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f))) P hP hreg_0 =
    evalRatFunAt 0 P hP hreg_0' := by
    congr 1
  rw [this]
  exact evalRatFunAt_zero P hP hreg_0'

end Theorem158
