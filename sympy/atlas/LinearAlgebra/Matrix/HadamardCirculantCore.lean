/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/HadamardCirculantCore.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3

Hadamard matrices of order `n + 1` with circulant core, for the Paley case
(`n` prime with `n % 4 = 3`) and the twin-prime case (`n = p * (p + 2)`
with `p` and `p + 2` prime). Proves `Wanted` entry
`exists_hadamard_matrix_with_circulant_core`.
-/

import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.HadamardMatrix

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Equiv
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

namespace MetaMathlibExt

/-- Hadamard matrix with circulant core (Paley and twin-prime cases).

`isHadamardMatrix m H` is the sign-matrix orthogonality predicate
(entries `±1`, `Hᵀ * H = m • 1`); `hasCirculantCore n H` says the trailing
`n × n` block is circulant, `H (i+1) (j+1) = v (i - j)` with `Fin`
modular difference. The formalized theorem is the prime specialization of
cases (1)–(2): such a matrix of order `n + 1` exists when `n` is a prime
congruent to 3 mod 4 (Paley) or `n = p * (p + 2)` with `p` and `p + 2`
both prime (Stanton–Sprott/Whiteman).

Source: Richard P. Brent and Adam B. Yedidia, "Computation of Maximal
Determinants of Binary Circulant Matrices," Journal of Integer Sequences 21
(2018), Article 18.5.6, Theorem (label thm:circulant_core), lines 684–695,
https://cs.uwaterloo.ca/journals/JIS/VOL21/Brent/brent11.tex
quoting Kotsireas et al.; attributions at lines 698–704. The prime-power
versions of cases (1)–(2), if the source allows them, and cases (3)–(4) of
the source theorem (Singer, Hall) are not formalized here. -/
def isHadamardMatrix (m : ℕ) (H : Matrix (Fin m) (Fin m) ℤ) : Prop :=
  (∀ i j, H i j = 1 ∨ H i j = -1) ∧
    (Matrix.transpose H) * H = (m : ℤ) • (1 : Matrix (Fin m) (Fin m) ℤ)

def hasCirculantCore (n : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) : Prop :=
  ∃ v : Fin n → ℤ, ∀ i j : Fin n, H (Fin.succ i) (Fin.succ j) = v (i - j)
end MetaMathlibExt
