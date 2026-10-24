import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.ABBoundarySquareRoot
open Filter Finset Set SimpleGraph Topology StatMech StatMech.Sharpness


/--
[abbs_latticeCoupling_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundarySquareRoot.lean)
-/
@[path]
private lemma abbs_latticeCoupling_translate_eq
  {d : Nat}
  {x u v : Site d} :
-- imply
  abblLatticeCoupling d s(FK.fktc_translate x u, FK.fktc_translate x v) = abblLatticeCoupling d s(u, v) := by
-- proof
  apply StatMech.Sharpness.abbs_latticeCoupling_translate x u v

/--
[abbs_latticeCoupling_row_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundarySquareRoot.lean)
-/
@[path]
private lemma abbs_latticeCoupling_row_summable_eq
  {d : Nat}
  {x : Site d} :
-- imply
  Summable (fun y ↦ if (hypercubicLattice d).Adj x y then abblLatticeCoupling d s(x, y) else 0) := by
-- proof
  apply StatMech.Sharpness.abbs_latticeCoupling_row_summable x

/--
[abbs_latticeCoupling_row_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundarySquareRoot.lean)
-/
@[path]
private lemma abbs_latticeCoupling_row_tsum_eq
  {d : Nat}
  {x : Site d} :
-- imply
  (∑' y, if (hypercubicLattice d).Adj x y then abblLatticeCoupling d s(x, y) else 0) = (2 * d : Real) := by
-- proof
  apply StatMech.Sharpness.abbs_latticeCoupling_row_tsum x

/--
[abbs_latticeCoupling_window_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundarySquareRoot.lean)
-/
@[path]
private lemma abbs_latticeCoupling_window_row_eq
  {d : Nat}
  {S : Finset (Site d)}
  {x : S} :
-- imply
  abcrIncidentCoupling (abigWindowGraph (hypercubicLattice d) S) (abigWindowCoupling (abblLatticeCoupling d) S) x ≤ (2 * d : Real) := by
-- proof
  apply StatMech.Sharpness.abbs_latticeCoupling_window_row S x

/--
[abbs_forward_characteristic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundarySquareRoot.lean)
-/
@[path]
private lemma abbs_forward_characteristic_eq
  {d : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 < h) :
-- imply
  ∀ epsilon, 0 < epsilon → ∃ delta > 0, ∀ t ∈ Icc (0 : Real) delta, abigMag (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d) (beta + t) h ≤ abigMag (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d) beta (h + ((2 * d : Real) * (abigMag (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d) beta h + epsilon)) * t) := by
-- proof
  apply StatMech.Sharpness.abbs_forward_characteristic beta h hbeta hh

/--
[abbs_finite_integratingFactor_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundarySquareRoot.lean)
-/
@[path]
private lemma abbs_finite_integratingFactor_antitone_eq
  {d n : Nat}
-- given
  (hn : 0 < n)
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hcrit : tildePc d ≤ bondParam beta) :
-- imply
  AntitoneOn (fun b ↦ b * (1 - abbMag d n b h)) (Ici beta) := by
-- proof
  apply StatMech.Sharpness.abbs_finite_integratingFactor_antitone hn beta h hbeta hh hcrit

/--
[abbs_infinite_integratingFactor_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundarySquareRoot.lean)
-/
@[path]
private lemma abbs_infinite_integratingFactor_antitone_eq
  {d : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 < h)
  (hcrit : tildePc d ≤ bondParam beta) :
-- imply
  AntitoneOn (fun b ↦ b * (1 - abigMag (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d) b h)) (Ici beta) := by
-- proof
  apply StatMech.Sharpness.abbs_infinite_integratingFactor_antitone beta h hbeta hh hcrit

/--
[abbs_infinite_field_meanfield](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundarySquareRoot.lean)
-/
@[path]
private lemma abbs_infinite_field_meanfield_eq
  {d : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 < h)
  (hcrit : tildePc d ≤ bondParam beta) :
-- imply
  1 - abigMag (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d) beta h ≤ beta * (2 * d : Real) * (abigMag (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d) beta h * deriv (fun t ↦ abigMag (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d) beta t) h) := by
-- proof
  apply StatMech.Sharpness.abbs_infinite_field_meanfield beta h hbeta hh hcrit

/--
[abbs_field_sq_lower_bound_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundarySquareRoot.lean)
-/
@[path]
private lemma abbs_field_sq_lower_bound_pos_eq
  {K : Real}
  {m : Real → Real}
-- given
  (hK : 0 < K)
  (hdiff : ∀ h ∈ Ioi (0 : Real), DifferentiableAt Real m h)
  (hmono : ∀ h ∈ Ioi (0 : Real), 0 ≤ deriv m h)
  (heq : ∀ h ∈ Ioi (0 : Real), 1 - m h ≤ K * (m h * deriv m h))
  (h₀ : Real)
  (hh₀ : 0 < h₀)
  (hle : m h₀ ≤ 1 / 2) :
-- imply
  h₀ / K ≤ (m h₀) ^ 2 := by
-- proof
  apply StatMech.Sharpness.abbs_field_sq_lower_bound_pos K hK m hdiff hmono heq h₀ hh₀ hle

/--
[abbs_field_sqrt_lower_bound_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundarySquareRoot.lean)
-/
@[path]
private lemma abbs_field_sqrt_lower_bound_pos_eq
  {K : Real}
  {m : Real → Real}
-- given
  (hK : 0 < K)
  (hdiff : ∀ h ∈ Ioi (0 : Real), DifferentiableAt Real m h)
  (hmono : ∀ h ∈ Ioi (0 : Real), 0 ≤ deriv m h)
  (hmnn : ∀ h, 0 ≤ m h)
  (heq : ∀ h ∈ Ioi (0 : Real), 1 - m h ≤ K * (m h * deriv m h)) :
-- imply
  ∃ c > 0, ∀ h ∈ Ioc (0 : Real) (K / 4), c * Real.sqrt h ≤ m h := by
-- proof
  apply StatMech.Sharpness.abbs_field_sqrt_lower_bound_pos K hK m hdiff hmono hmnn heq

/--
[abbs_perco_meanfield_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundarySquareRoot.lean)
-/
@[path]
private lemma abbs_perco_meanfield_sqrt_eq
  {d : Nat}
  {beta : Real}
-- given
  (hd : 0 < d)
  (hbeta : 0 < beta)
  (hcrit : tildePc d ≤ bondParam beta) :
-- imply
  ∃ c > 0, ∀ h ∈ Ioc (0 : Real) (beta * (2 * d : Real) / 4), c * Real.sqrt h ≤ abigMag (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d) beta h := by
-- proof
  apply StatMech.Sharpness.abbs_perco_meanfield_sqrt hd beta hbeta hcrit

/--
[abbs_perco_meanfield_sqrt_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundarySquareRoot.lean)
-/
@[path]
private lemma abbs_perco_meanfield_sqrt_critical_eq
  {d : Nat}
-- given
  (hd : 0 < d)
  (htc1 : (tildePc d : Real) < 1) :
-- imply
  ∃ c > 0, ∀ h ∈ Ioc (0 : Real) (betaTildeC d 1 * (2 * d : Real) / 4), c * Real.sqrt h ≤ abigMag (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d) (betaTildeC d 1) h := by
-- proof
  apply StatMech.Sharpness.abbs_perco_meanfield_sqrt_critical hd htc1

/--
[abbs_perco_meanfield_sqrt_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundarySquareRoot.lean)
-/
@[path]
private lemma abbs_perco_meanfield_sqrt_unconditional_eq
  {d : Nat}
-- given
  (hd : 2 ≤ d) :
-- imply
  ∃ c > 0, ∀ h ∈ Ioc (0 : Real) (betaTildeC d 1 * (2 * d : Real) / 4), c * Real.sqrt h ≤ abigMag (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d) (betaTildeC d 1) h := by
-- proof
  apply StatMech.Sharpness.abbs_perco_meanfield_sqrt_unconditional hd


-- created on 2026-10-23
