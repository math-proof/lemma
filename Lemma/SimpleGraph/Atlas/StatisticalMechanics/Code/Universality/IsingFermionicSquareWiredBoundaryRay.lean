import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredBoundaryRay.Part2
open StatMech StatMech.Universality StatMech.Universality.FKIsingDobrushinDomain


/--
[fermionicObservable_eq_signedExplorationMass_mul_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryRay.lean)
-/
@[path]
private lemma fermionicObservable_eq_signedExplorationMass_mul_phase_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {e : M}
  {phase : Complex}
-- given
  (hphase : ∀ omega, e ∈ D.exploration omega → D.windingPhase omega e ^ 2 = phase ^ 2) :
-- imply
  D.fermionicObservable e = (D.signedExplorationMass e phase : Complex) * phase := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.fermionicObservable_eq_signedExplorationMass_mul_phase D e phase hphase

/--
[exists_nonnegative_boundary_square_of_phase_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryRay.lean)
-/
@[path]
private lemma exists_nonnegative_boundary_square_of_phase_sq_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {e : M}
  {normal phase : Complex}
  {r : Real}
-- given
  (hphase : ∀ omega, e ∈ D.exploration omega → D.windingPhase omega e ^ 2 = phase ^ 2)
  (hr : 0 ≤ r)
  (hline : normal * phase ^ 2 = (r : Complex)) :
-- imply
  ∃ t : Real, 0 ≤ t ∧ normal * D.fermionicObservable e ^ 2 = (t : Complex) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.exists_nonnegative_boundary_square_of_phase_sq D e normal phase r hphase hr hline

/--
[fkIsingSquare_exp_turn_modEq_eight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryRay.lean)
-/
@[path]
private lemma fkIsingSquare_exp_turn_modEq_eight_eq
  {a b : Int}
-- given
  (h : a ≡ b [ZMOD 8]) :
-- imply
  Complex.exp (Complex.I * (((a : Real) * (Real.pi / 4) : Real) : Complex)) = Complex.exp (Complex.I * (((b : Real) * (Real.pi / 4) : Real) : Complex)) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_exp_turn_modEq_eight a b h

/--
[fkIsingSquareWiredDirectedTangent_mul_phase_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryRay.lean)
-/
@[path]
private lemma fkIsingSquareWiredDirectedTangent_mul_phase_sq_eq
  {n : Nat}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredDirectedTangent n hn z * fkIsingSquareWiredDirectedPhase n hn z ^ 2 = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredDirectedTangent_mul_phase_sq n hn z

/--
[fkIsingSquareWired_windingPhase_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryRay.lean)
-/
@[path]
private lemma fkIsingSquareWired_windingPhase_sq_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hz : z ∈ fkIsingSquareWiredExplorationOrder n hn omega) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).windingPhase omega z ^ 2 = fkIsingSquareWiredDirectedPhase n hn z ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_windingPhase_sq n hn omega z hz

/--
[fkIsingSquareWired_exists_nonnegative_directed_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryRay.lean)
-/
@[path]
private lemma fkIsingSquareWired_exists_nonnegative_directed_square_eq
  {n : Nat}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  ∃ t : Real, 0 ≤ t ∧ fkIsingSquareWiredDirectedTangent n hn z * (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable z ^ 2 = (t : Complex) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_exists_nonnegative_directed_square n hn z


-- created on 2026-10-23
