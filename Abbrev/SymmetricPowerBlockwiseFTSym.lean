import Def.SymmetricPowerPowerSeriesFTSym

set_option autoImplicit false

noncomputable section

namespace MvPowerSeries

open FixedPoints

universe u

variable (k : Type u) [CommRing k]

section BlockIn

variable (m : ℕ) (rs : Fin (m + 1) → ℕ)

abbrev stepIdx : Fin (∑ j, (rs ∘ Fin.castSucc) j) ⊕ Fin (rs (Fin.last m)) ≃ Fin (∑ j, rs j) :=
  finSumFinEquiv.trans (finCongr (Fin.sum_univ_castSucc rs).symm)

end BlockIn

variable {m : ℕ} {rs : Fin m → ℕ}

namespace BlockwiseFTSym

abbrev toBlock (l : Fin (∑ j, rs j)) : (j : Fin m) × Fin (rs j) :=
  (finSigmaFinEquiv (n := rs)).symm l

end BlockwiseFTSym

namespace BlockwiseFTSym

section MapFixedPoints

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]
  {σ : Type*}

end MapFixedPoints

section Step

variable (k) {m : ℕ} (rs : Fin (m + 1) → ℕ)

end Step

section StepEquivariance

variable (k : Type u) [CommRing k] {m : ℕ} (rs : Fin (m + 1) → ℕ)

end StepEquivariance

end BlockwiseFTSym

open BlockwiseFTSym

variable (k) (m : ℕ) (rs : Fin m → ℕ)

end MvPowerSeries
