import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.SLE.LoewnerCapacity
open Complex Set Filter Topology StatMech StatMech.SLE


/--
[tendsto_self_div_of_tendsto_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerCapacity.lean)
-/
@[path]
private lemma tendsto_self_div_of_tendsto_const_eq
  {F : ℂ → ℂ}
  {c : ℂ}
-- given
  (hF : Tendsto (fun z => F z - z) (cocompact ℂ) (𝓝 c)) :
-- imply
  Tendsto (fun z => z / F z) (cocompact ℂ) (𝓝 1) := by
-- proof
  apply StatMech.SLE.tendsto_self_div_of_tendsto_const F c hF

/--
[tendsto_mul_loewnerField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerCapacity.lean)
-/
@[path]
private lemma tendsto_mul_loewnerField_eq
  {W : ℝ → ℝ}
  {t : ℝ}
  {G : ℂ → ℂ}
-- given
  (hG : Tendsto (fun z => G z - z) (cocompact ℂ) (𝓝 0)) :
-- imply
  Tendsto (fun z => z * loewnerField W t (G z)) (cocompact ℂ) (𝓝 (2 : ℂ)) := by
-- proof
  apply StatMech.SLE.tendsto_mul_loewnerField W t G hG

/--
[coeff_ode_solution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerCapacity.lean)
-/
@[path]
private lemma coeff_ode_solution_eq
  {a₁ : ℝ → ℝ}
-- given
  (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t)
  (h0 : a₁ 0 = 0) :
-- imply
  ∀ t ∈ Ici (0 : ℝ), a₁ t = 2 * t := by
-- proof
  apply StatMech.SLE.coeff_ode_solution hd h0

/--
[hasHalfPlaneCapacity_zero_of_eq_id](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerCapacity.lean)
-/
@[path]
private lemma hasHalfPlaneCapacity_zero_of_eq_id_eq
  {g : ℝ → ℂ → ℂ}
-- given
  (h0 : ∀ z, g 0 z = z) :
-- imply
  HasHalfPlaneCapacity (g 0) 0 := by
-- proof
  apply StatMech.SLE.hasHalfPlaneCapacity_zero_of_eq_id h0

/--
[loewner_halfplane_capacity_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerCapacity.lean)
-/
@[path]
private lemma loewner_halfplane_capacity_eq_eq
  {g : ℝ → ℂ → ℂ}
  {a₁ : ℝ → ℝ}
-- given
  (hcap : ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (a₁ t))
  (h0 : a₁ 0 = 0)
  (hrate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t) :
-- imply
  ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (2 * t) := by
-- proof
  apply StatMech.SLE.loewner_halfplane_capacity_eq hcap h0 hrate

/--
[loewner_capacity_coeff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerCapacity.lean)
-/
@[path]
private lemma loewner_capacity_coeff_eq_eq
  {a₁ : ℝ → ℝ}
-- given
  (h0 : a₁ 0 = 0)
  (hrate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t) :
-- imply
  ∀ t ∈ Ici (0 : ℝ), a₁ t = 2 * t := by
-- proof
  apply StatMech.SLE.loewner_capacity_coeff_eq h0 hrate

/--
[loewner_capacity_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerCapacity.lean)
-/
@[path]
private lemma loewner_capacity_unique_eq
  {g : ℝ → ℂ → ℂ}
  {a₁ : ℝ → ℝ}
  {t : ℝ}
  {b : ℝ}
-- given
  (hcap : ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (a₁ t))
  (h0 : a₁ 0 = 0)
  (hrate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t)
  (ht : t ∈ Ici (0 : ℝ))
  (hb : HasHalfPlaneCapacity (g t) b) :
-- imply
  b = 2 * t := by
-- proof
  apply StatMech.SLE.loewner_capacity_unique hcap h0 hrate ht hb

/--
[loewner_capacity_eq_of_loewnerChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerCapacity.lean)
-/
@[path]
private lemma loewner_capacity_eq_of_loewnerChain_eq
  {c : LoewnerChain}
  {a₁ : ℝ → ℝ}
-- given
  (hcap : ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (c.maps t) (a₁ t))
  (hrate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t) :
-- imply
  ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (c.maps t) (2 * t) := by
-- proof
  apply StatMech.SLE.loewner_capacity_eq_of_loewnerChain c hcap hrate


-- created on 2026-10-23
