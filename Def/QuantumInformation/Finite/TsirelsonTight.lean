/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/QuantumInformation/Finite/TsirelsonTight.lean -/

/-
Source: B. S. Cirel'son/Tsirelson, "Quantum generalizations of Bell's inequality",
  Letters in Mathematical Physics 4(2) (1980), 93-100, DOI 10.1007/BF00417500.
Proof: standard 4x4 CHSH observables (Pauli-type block matrices with
  `s = 1/√2` coefficients); the vector `[s, 0, 0, s]` is an eigenvector of the
  CHSH operator with eigenvalue `2√2`. Every explicit matrix product,
  self-adjointness, commutation, and involution identity below was checked
  entry by entry against the archive candidate before retention.
-/

import Mathlib.Algebra.Star.CHSH
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
open Matrix


namespace MathlibExt.QuantumInformation.Finite.TsirelsonTight

noncomputable def s : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

noncomputable def u : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

def A₀ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

def A₁ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

noncomputable def B₀ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![s, s, 0, 0; s, -s, 0, 0; 0, 0, s, s; 0, 0, s, -s]

noncomputable def B₁ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![s, -s, 0, 0; -s, -s, 0, 0; 0, 0, s, -s; 0, 0, -s, -s]

noncomputable def v : Fin 4 → ℂ := ![s, 0, 0, s]

end MathlibExt.QuantumInformation.Finite.TsirelsonTight
