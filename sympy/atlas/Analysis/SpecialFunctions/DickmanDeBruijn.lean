/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean -/

import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The Dickman–de Bruijn function

This file defines a reusable predicate characterizing the Dickman–de Bruijn function on `ℝ`.
It records the standard zero extension to negative inputs, its range and continuity on
nonnegative inputs, its normalization on `[0, 1]`, and its delay differential equation above
one. Existence and uniqueness are proved separately in
`MathlibExt.Analysis.SpecialFunctions.DickmanDeBruijnExistsUnique`.

## References

* [Ofir Gorodetsky, *Rigidity of Averages over the Two Largest Prime
  Factors*](https://arxiv.org/abs/2608.05191)
* [Jared Duker Lichtman, *An improvement on the largest prime factors of consecutive
  integers*](https://arxiv.org/abs/2607.16032)
-/

namespace Real

/-- `IsDickmanDeBruijn ρ` says that `ρ` is the Dickman–de Bruijn function, extended by zero to
negative inputs. Continuity is asserted only on the original nonnegative domain, since the total
zero extension is discontinuous at zero. -/
def IsDickmanDeBruijn (ρ : ℝ → ℝ) : Prop :=
  (∀ u, u < 0 → ρ u = 0) ∧
    Set.MapsTo ρ (Set.Ici (0 : ℝ)) (Set.Icc (0 : ℝ) 1) ∧
    ContinuousOn ρ (Set.Ici (0 : ℝ)) ∧
    (∀ u ∈ Set.Icc (0 : ℝ) 1, ρ u = 1) ∧
    ∀ u, 1 < u → DifferentiableAt ℝ ρ u ∧ u * deriv ρ u + ρ (u - 1) = 0

/-- A Dickman–de Bruijn function vanishes at negative arguments. -/
lemma IsDickmanDeBruijn.eq_zero_of_neg {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) {u : ℝ} (hu : u < 0) : ρ u = 0 :=
  h.1 u hu

/-- A Dickman–de Bruijn function maps nonnegative inputs into `[0, 1]`. -/
lemma IsDickmanDeBruijn.mapsTo_Ici_Icc {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) :
    Set.MapsTo ρ (Set.Ici (0 : ℝ)) (Set.Icc (0 : ℝ) 1) :=
  h.2.1

/-- A Dickman–de Bruijn function is continuous on the nonnegative reals. -/
lemma IsDickmanDeBruijn.continuousOn_Ici {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) : ContinuousOn ρ (Set.Ici (0 : ℝ)) :=
  h.2.2.1

/-- A Dickman–de Bruijn function equals one on `[0, 1]`. -/
lemma IsDickmanDeBruijn.eq_one_of_mem_Icc {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) : ρ u = 1 :=
  h.2.2.2.1 u hu

/-- Inequality form of the normalization of a Dickman–de Bruijn function on `[0, 1]`. -/
lemma IsDickmanDeBruijn.eq_one_of_nonneg_of_le_one {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : ρ u = 1 :=
  h.eq_one_of_mem_Icc ⟨h0, h1⟩

/-- A Dickman–de Bruijn function is differentiable above one. -/
lemma IsDickmanDeBruijn.differentiableAt_of_one_lt {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) {u : ℝ} (hu : 1 < u) : DifferentiableAt ℝ ρ u :=
  (h.2.2.2.2 u hu).1

/-- The Dickman–de Bruijn delay differential equation above one. -/
lemma IsDickmanDeBruijn.delay_eq {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) {u : ℝ} (hu : 1 < u) :
    u * deriv ρ u + ρ (u - 1) = 0 :=
  (h.2.2.2.2 u hu).2

/-- A Dickman–de Bruijn function is nonnegative at nonnegative arguments. -/
lemma IsDickmanDeBruijn.nonneg_of_nonneg {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ ρ u :=
  (h.mapsTo_Ici_Icc hu).1

/-- A Dickman–de Bruijn function is at most one at nonnegative arguments. -/
lemma IsDickmanDeBruijn.le_one_of_nonneg {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) {u : ℝ} (hu : 0 ≤ u) : ρ u ≤ 1 :=
  (h.mapsTo_Ici_Icc hu).2

/-- The range bound for a Dickman–de Bruijn function at a nonnegative argument. -/
lemma IsDickmanDeBruijn.mem_Icc_of_nonneg {ρ : ℝ → ℝ}
    (h : IsDickmanDeBruijn ρ) {u : ℝ} (hu : 0 ≤ u) : ρ u ∈ Set.Icc (0 : ℝ) 1 :=
  h.mapsTo_Ici_Icc hu

end Real
