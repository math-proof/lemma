import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.ZeroBetaDLRUniqueness
open MeasureTheory Set StatMech StatMech.Ising


/--
[fvProb_zero_beta_boundary_independent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ZeroBetaDLRUniqueness.lean)
-/
@[path]
private lemma fvProb_zero_beta_boundary_independent_eq
  {d : Nat}
  {eta zeta : ConfigSpace (Site d)}
  {n : Nat}
  {B : Finset (Sym2 (Site d))}
-- given
  (h : Real)
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  fvProb eta n B 0 h tau = fvProb zeta n B 0 h tau := by
-- proof
  apply StatMech.Ising.fvProb_zero_beta_boundary_independent eta zeta n B h tau

/--
[specApply_zero_beta_boundary_independent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ZeroBetaDLRUniqueness.lean)
-/
@[path]
private lemma specApply_zero_beta_boundary_independent_eq
  {d : Nat}
  {eta zeta : ConfigSpace (Site d)}
  {n : Nat}
  {B : Finset (Sym2 (Site d))}
  {f : ConfigSpace (Site d) → Real}
-- given
  (h : Real)
  (hf : ∀ omega omega', (∀ x ∈ box d n, omega x = omega' x) → f omega = f omega') :
-- imply
  specApply n B 0 h f eta = specApply n B 0 h f zeta := by
-- proof
  apply StatMech.Ising.specApply_zero_beta_boundary_independent eta zeta n B h f hf

/--
[multiOpen_indicator_eq_of_eqOn_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ZeroBetaDLRUniqueness.lean)
-/
@[path]
private lemma multiOpen_indicator_eq_of_eqOn_box_eq
  {d : Nat}
  {T : Finset (Site d)}
  {n : Nat}
  {omega omega' : ConfigSpace (Site d)}
-- given
  (hT : (T : Set (Site d)) ⊆ box d n)
  (heq : ∀ x ∈ box d n, omega x = omega' x) :
-- imply
  (fmu_multiOpen T).indicator (fun _ => (1 : Real)) omega = (fmu_multiOpen T).indicator (fun _ => (1 : Real)) omega' := by
-- proof
  apply StatMech.Ising.multiOpen_indicator_eq_of_eqOn_box T n hT omega omega' heq

/--
[isDLRState_eq_of_zero_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ZeroBetaDLRUniqueness.lean)
-/
@[path]
private lemma isDLRState_eq_of_zero_beta_eq
  {d : Nat}
  {mu nu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
  [IsProbabilityMeasure nu]
-- given
  (h : Real)
  (hmu : IsDLRState d 0 h mu)
  (hnu : IsDLRState d 0 h nu) :
-- imply
  mu = nu := by
-- proof
  apply StatMech.Ising.isDLRState_eq_of_zero_beta h mu nu hmu hnu

/--
[gibbs_unique_zero_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ZeroBetaDLRUniqueness.lean)
-/
@[path]
private lemma gibbs_unique_zero_beta_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
-- given
  (h : Real)
  (hmu : IsDLRState d 0 h mu) :
-- imply
  mu = (minusState d 0 h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.gibbs_unique_zero_beta h mu hmu


-- created on 2026-10-23
