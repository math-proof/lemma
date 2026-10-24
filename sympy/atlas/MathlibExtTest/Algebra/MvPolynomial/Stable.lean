/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/MvPolynomial/Stable.lean -/


import sympy.atlas.Algebra.MvPolynomial.Stable
import Lemma.MvPolynomial.Stable


open scoped ComplexOrder

open MvPolynomial

namespace MathlibExtTest.Algebra.MvPolynomial.Stable

-- A nonempty list of mixed differential operators preserves stability.
example :
    (mixedDifferential [()] (X () : MvPolynomial Unit ℂ)).IsStable :=
  MvPolynomial.IsStable.mixedDifferential unitX_isStable [()]

-- A nonempty mixed differential preserves real stability.
example :
    (mixedDifferential [()] (X () : MvPolynomial Unit ℂ)).IsRealStable :=
  MvPolynomial.IsRealStable.mixedDifferential unitX_isRealStable [()]

-- Specialization turns the partial derivative of a quadratic into its derivative.
example :
    univariateSpecialization () (fun _ ↦ (2 : ℤ))
        (pderiv () ((X () : MvPolynomial Unit ℤ) ^ 2 + C 3)) =
      Polynomial.derivative
        (univariateSpecialization () (fun _ ↦ (2 : ℤ))
          ((X () : MvPolynomial Unit ℤ) ^ 2 + C 3)) :=
  derivative_univariateSpecialization () (fun _ ↦ (2 : ℤ)) _

-- Evaluating a specialization updates the selected variable.
example :
    Polynomial.eval 5
        (univariateSpecialization () (fun _ ↦ (2 : ℤ))
          ((X () : MvPolynomial Unit ℤ) ^ 2 + C 3)) =
      eval (Function.update (fun _ ↦ (2 : ℤ)) () 5)
        ((X () : MvPolynomial Unit ℤ) ^ 2 + C 3) :=
  eval_univariateSpecialization () (fun _ ↦ (2 : ℤ)) 5 _

-- A specialization of a real-coefficient affine polynomial is conjugation-invariant.
example :
    Polynomial.map (starRingEnd ℂ)
        (univariateSpecialization () (fun _ ↦ (3 : ℂ))
          ((X () : MvPolynomial Unit ℂ) + C 2)) =
      univariateSpecialization () (fun _ ↦ (3 : ℂ))
        ((X () : MvPolynomial Unit ℂ) + C 2) := by
  apply MvPolynomial.map_star_univariateSpecialization
  · have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      apply Complex.ext <;> norm_num
    simp [htwo]
  · intro j hne
    exact (hne rfl).elim

-- Roots of the specialization of `X` lie in the closed lower half-plane.
example :
    ∀ w ∈ (univariateSpecialization () (fun _ ↦ (0 : ℂ))
      (X () : MvPolynomial Unit ℂ)).roots, w.im ≤ 0 := by
  apply MvPolynomial.IsStable.roots_im_nonpos_univariateSpecialization unitX_isStable
  · intro j hne
    exact (hne rfl).elim
  · simp [univariateSpecialization]

-- Real specialization makes the stable polynomial `X` real-rooted.
example :
    (univariateSpecialization () (fun _ ↦ (0 : ℂ))
      (X () : MvPolynomial Unit ℂ)).IsRealRooted := by
  apply MvPolynomial.isRealRooted_univariateSpecialization_of_isRealStable () _
      unitX_isRealStable 1
  · intro x
    simp [univariateSpecialization]
  · intro x
    simp [univariateSpecialization]
  · intro j hne
    exact (hne rfl).elim

-- Applying `1 - ∂` to `X` preserves stability.
example :
    ((X () : MvPolynomial Unit ℂ) - pderiv () (X ())).IsStable :=
  MvPolynomial.IsStable.sub_pderiv unitX_isStable ()

-- Applying `1 - ∂` to the real-stable polynomial `X` preserves real stability.
example :
    ((X () : MvPolynomial Unit ℂ) - pderiv () (X ())).IsRealStable :=
  MvPolynomial.IsRealStable.sub_pderiv unitX_isRealStable ()

end MathlibExtTest.Algebra.MvPolynomial.Stable
