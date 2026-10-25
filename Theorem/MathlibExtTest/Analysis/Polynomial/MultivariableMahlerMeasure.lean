/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Polynomial/MultivariableMahlerMeasure.lean -/


import sympy.atlas.Analysis.Polynomial.MultivariableMahlerMeasure
open Complex MeasureTheory
open scoped Real


namespace LogarithmicMahlerMeasure

-- The zero-dimensional torus evaluates a constant correctly.
example (θ : Fin 0 → ℝ) (c : ℂ) :
    torusEval θ (AddMonoidAlgebra.single 0 c) = c := by
  exact torusEval_single_zero θ c

-- Positive and negative exponents have the expected sign at `π / 2`.
example :
    torusEval (fun _ : Fin 1 => Real.pi / 2)
      (AddMonoidAlgebra.single (fun _ : Fin 1 => (1 : ℤ)) (1 : ℂ)) = Complex.I := by
  rw [torusEval_single, one_mul]
  have hChar : torusCharacter (fun _ : Fin 1 => Real.pi / 2)
      (fun _ : Fin 1 => (1 : ℤ)) = Complex.I := by
    unfold torusCharacter realSum
    have hSum : (∑ j : Fin 1, ((fun _ : Fin 1 => (1 : ℤ)) j : ℝ) *
        (fun _ : Fin 1 => Real.pi / 2) j) = Real.pi / 2 := by
      rw [Fintype.sum_unique]
      simp
    rw [hSum]
    have hComm : Complex.I * ((Real.pi / 2 : ℝ) : ℂ) =
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by ring
    rw [hComm, Complex.exp_ofReal_mul_I]
    simp
  exact hChar

example :
    torusEval (fun _ : Fin 1 => Real.pi / 2)
      (AddMonoidAlgebra.single (fun _ : Fin 1 => (-1 : ℤ)) (1 : ℂ)) = -Complex.I := by
  rw [torusEval_single, one_mul]
  have hChar : torusCharacter (fun _ : Fin 1 => Real.pi / 2)
      (fun _ : Fin 1 => (-1 : ℤ)) = -Complex.I := by
    unfold torusCharacter realSum
    have hSum : (∑ j : Fin 1, ((fun _ : Fin 1 => (-1 : ℤ)) j : ℝ) *
        (fun _ : Fin 1 => Real.pi / 2) j) = -(Real.pi / 2) := by
      rw [Fintype.sum_unique]
      simp
    rw [hSum]
    have hComm : Complex.I * ((-(Real.pi / 2) : ℝ) : ℂ) =
        ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I := by ring
    rw [hComm, Complex.exp_ofReal_mul_I]
    simp [Real.cos_neg, Real.sin_neg]
  exact hChar

-- The exponent is coordinate-sensitive in two variables.
example :
    torusEval (fun i : Fin 2 => if i = 0 then Real.pi / 2 else 0)
      (AddMonoidAlgebra.single (fun i : Fin 2 => if i = 0 then (1 : ℤ) else 0) (1 : ℂ)) =
        Complex.I := by
  rw [torusEval_single, one_mul]
  have hChar : torusCharacter (fun i : Fin 2 => if i = 0 then Real.pi / 2 else 0)
      (fun i : Fin 2 => if i = 0 then (1 : ℤ) else 0) = Complex.I := by
    unfold torusCharacter realSum
    have hSum : (∑ j : Fin 2,
        ((fun i : Fin 2 => if i = 0 then (1 : ℤ) else 0) j : ℝ) *
          (fun i : Fin 2 => if i = 0 then Real.pi / 2 else (0 : ℝ)) j) =
        Real.pi / 2 := by
      simp
    rw [hSum]
    have hComm : Complex.I * ((Real.pi / 2 : ℝ) : ℂ) =
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by ring
    rw [hComm, Complex.exp_ofReal_mul_I]
    simp
  exact hChar

example :
    torusEval (fun i : Fin 2 => if i = 0 then Real.pi / 2 else 0)
      (AddMonoidAlgebra.single (fun i : Fin 2 => if i = 0 then (0 : ℤ) else 1) (1 : ℂ)) = 1 := by
  rw [torusEval_single, one_mul]
  have hChar : torusCharacter (fun i : Fin 2 => if i = 0 then Real.pi / 2 else 0)
      (fun i : Fin 2 => if i = 0 then (0 : ℤ) else 1) = 1 := by
    unfold torusCharacter realSum
    have hSum : (∑ j : Fin 2,
        ((fun i : Fin 2 => if i = 0 then (0 : ℤ) else 1) j : ℝ) *
          (fun i : Fin 2 => if i = 0 then Real.pi / 2 else (0 : ℝ)) j) = 0 := by
      simp
    rw [hSum]
    simp
  exact hChar

-- The algebra-hom interface and the one-variable Laurent bridge are usable downstream.
example {n : ℕ} (θ : Fin n → ℝ) (F G : AddMonoidAlgebra ℂ (Fin n → ℤ)) :
    torusEval θ (F * G) = torusEval θ F * torusEval θ G :=
  map_mul (torusEval θ) F G

example (c : ℂ) (k : ℤ) :
    bridgeLaurent (AddMonoidAlgebra.single (fun _ : Fin 1 => k) c) =
      AddMonoidAlgebra.single k c := by
  simp

-- The totalized logarithmic measure agrees with the expected zero and unit values.
example {m : ℕ} (c : ℂ) :
    logarithmicMahlerMeasure
      (AddMonoidAlgebra.single (0 : Fin m → ℤ) c) = Real.log ‖c‖ := by
  simp

example : logarithmicMahlerMeasure (0 : AddMonoidAlgebra ℂ (Fin 2 → ℤ)) = 0 := by
  simp

example : logarithmicMahlerMeasure (1 : AddMonoidAlgebra ℂ (Fin 2 → ℤ)) = 0 := by
  simp

end LogarithmicMahlerMeasure
