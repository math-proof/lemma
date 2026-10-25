import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexDelta_lt_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexDelta_lt_neg_one_eq
  {c : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexDelta c < -1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDelta_lt_neg_one hc

/--
[sixVertexThetaDenominator_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexThetaDenominator_pos_eq
  {c : ℝ}
  {x y : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexThetaDenominator c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexThetaDenominator_pos hc x y

/--
[sixVertexTheta_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexTheta_self_eq
  {c x : ℝ} :
-- imply
  sixVertexTheta c x x = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_self c x

/--
[sixVertexTheta_antisymm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexTheta_antisymm_eq
  {c x y : ℝ} :
-- imply
  sixVertexTheta c y x = -sixVertexTheta c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_antisymm c x y

/--
[sixVertexTheta_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexTheta_neg_eq
  {c x y : ℝ} :
-- imply
  sixVertexTheta c (-x) (-y) = -sixVertexTheta c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_neg c x y

/--
[sixVertexTheta_add_two_pi_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexTheta_add_two_pi_left_eq
  {c x y : ℝ} :
-- imply
  sixVertexTheta c (x + 2 * Real.pi) y = sixVertexTheta c x y - 2 * Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_add_two_pi_left c x y

/--
[sixVertexTheta_add_two_pi_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexTheta_add_two_pi_right_eq
  {c x y : ℝ} :
-- imply
  sixVertexTheta c x (y + 2 * Real.pi) = sixVertexTheta c x y + 2 * Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_add_two_pi_right c x y

/--
[sixVertexTheta_pi_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexTheta_pi_pair_eq
  {c y : ℝ} :
-- imply
  sixVertexTheta c Real.pi y + sixVertexTheta c Real.pi (-y) = -2 * Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_pi_pair c y

/--
[sixVertexTheta_neg_pi_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexTheta_neg_pi_pair_eq
  {c y : ℝ} :
-- imply
  sixVertexTheta c (-Real.pi) y + sixVertexTheta c (-Real.pi) (-y) = 2 * Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_neg_pi_pair c y

/--
[continuous_sixVertexTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma continuous_sixVertexTheta_eq
  {c : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  Continuous fun xy : ℝ × ℝ => sixVertexTheta c xy.1 xy.2 := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexTheta hc

/--
[hasDerivAt_sixVertexTheta_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexTheta_left_eq
  {c : ℝ}
  {x y : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  HasDerivAt (fun t => sixVertexTheta c t y) (4 * sixVertexDelta c * (Real.cos y - sixVertexDelta c) / (sixVertexThetaDenominator c x y ^ 2 + (Real.sin x - Real.sin y) ^ 2)) x := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexTheta_left hc x y

/--
[sixVertexTheta_left_deriv_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexTheta_left_deriv_neg_eq
  {c : ℝ}
  {x y : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  4 * sixVertexDelta c * (Real.cos y - sixVertexDelta c) / (sixVertexThetaDenominator c x y ^ 2 + (Real.sin x - Real.sin y) ^ 2) < 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_left_deriv_neg hc x y

/--
[strictAnti_sixVertexTheta_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma strictAnti_sixVertexTheta_left_eq
  {c : ℝ}
  {y : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  StrictAnti fun x => sixVertexTheta c x y := by
-- proof
  apply StatMech.FrontierD.strictAnti_sixVertexTheta_left hc y

/--
[strictMono_sixVertexTheta_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma strictMono_sixVertexTheta_right_eq
  {c : ℝ}
  {x : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  StrictMono fun y => sixVertexTheta c x y := by
-- proof
  apply StatMech.FrontierD.strictMono_sixVertexTheta_right hc x

/--
[sixVertexCentralQuantumNumber_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexCentralQuantumNumber_rev_eq
  {n : ℕ}
  {j : Fin n} :
-- imply
  sixVertexCentralQuantumNumber j.rev = -sixVertexCentralQuantumNumber j := by
-- proof
  apply StatMech.FrontierD.sixVertexCentralQuantumNumber_rev j

/--
[sixVertexCentralQuantumNumber_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexCentralQuantumNumber_eq_eq
  {n : ℕ}
  {j : Fin n} :
-- imply
  sixVertexCentralQuantumNumber j = (j.val : ℝ) - ((n : ℝ) - 1) / 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexCentralQuantumNumber_eq j

/--
[sum_sixVertexCentralQuantumNumber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sum_sixVertexCentralQuantumNumber_eq
  {n : ℕ} :
-- imply
  ∑ j : Fin n, sixVertexCentralQuantumNumber j = 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexCentralQuantumNumber n

/--
[strictMono_sixVertexCentralQuantumNumber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma strictMono_sixVertexCentralQuantumNumber_eq
  {n : ℕ} :
-- imply
  StrictMono (sixVertexCentralQuantumNumber : Fin n → ℝ) := by
-- proof
  apply StatMech.FrontierD.strictMono_sixVertexCentralQuantumNumber n

/--
[SixVertexRootSymmetric.reverse_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma reverse_neg_eq
  {n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hp : SixVertexRootSymmetric p) :
-- imply
  (fun j => -p j.rev) = p := by
-- proof
  apply StatMech.FrontierD.SixVertexRootSymmetric.reverse_neg hp

/--
[sum_sixVertexTheta_pi_of_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sum_sixVertexTheta_pi_of_symmetric_eq
  {c : ℝ}
  {n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hp : SixVertexRootSymmetric p) :
-- imply
  ∑ k, sixVertexTheta c Real.pi (p k) = -(n : ℝ) * Real.pi := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexTheta_pi_of_symmetric c hp

/--
[sum_sixVertexTheta_neg_pi_of_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sum_sixVertexTheta_neg_pi_of_symmetric_eq
  {c : ℝ}
  {n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hp : SixVertexRootSymmetric p) :
-- imply
  ∑ k, sixVertexTheta c (-Real.pi) (p k) = (n : ℝ) * Real.pi := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexTheta_neg_pi_of_symmetric c hp

/--
[sixVertexBetheUpdate_eq_self_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexBetheUpdate_eq_self_iff_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hN : 0 < N) :
-- imply
  sixVertexBetheUpdate c N n p = p ↔ SixVertexSatisfiesBetheEquations c N n p := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheUpdate_eq_self_iff hN p

/--
[continuous_sixVertexBetheUpdate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma continuous_sixVertexBetheUpdate_eq
  {c : ℝ}
  {N n : ℕ}
-- given
  (hc : 2 < c) :
-- imply
  Continuous fun p : Fin n → ℝ => sixVertexBetheUpdate c N n p := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexBetheUpdate hc N n

/--
[sixVertexBetheUpdate_reverse_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexBetheUpdate_reverse_neg_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
  {j : Fin n} :
-- imply
  sixVertexBetheUpdate c N n (fun k => -p k.rev) j = -sixVertexBetheUpdate c N n p j.rev := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheUpdate_reverse_neg c p j

/--
[sixVertexBetheUpdate_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexBetheUpdate_symmetric_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hp : SixVertexRootSymmetric p) :
-- imply
  SixVertexRootSymmetric (sixVertexBetheUpdate c N n p) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheUpdate_symmetric c hp

/--
[sixVertexBetheUpdate_mem_openInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexBetheUpdate_mem_openInterval_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hc : 2 < c)
  (hhalf : 2 * n ≤ N)
  (hsymm : SixVertexRootSymmetric p)
  (hinterval : SixVertexRootsInOpenInterval p) :
-- imply
  SixVertexRootsInOpenInterval (sixVertexBetheUpdate c N n p) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheUpdate_mem_openInterval hc hhalf hsymm hinterval

/--
[sixVertexBetheUpdate_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexBetheUpdate_strictMono_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hp : StrictMono p) :
-- imply
  StrictMono (sixVertexBetheUpdate c N n p) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheUpdate_strictMono hc hN hp

/--
[sixVertexBetheUpdate_strictMono_of_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexBetheUpdate_strictMono_of_monotone_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hp : Monotone p) :
-- imply
  StrictMono (sixVertexBetheUpdate c N n p) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheUpdate_strictMono_of_monotone hc hN hp

/--
[sixVertexClosedRootSimplex_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexClosedRootSimplex_nonempty_eq
  {n : ℕ} :
-- imply
  Set.Nonempty {p : Fin n → ℝ | SixVertexClosedRootSimplex p} := by
-- proof
  apply StatMech.FrontierD.sixVertexClosedRootSimplex_nonempty n

/--
[convex_sixVertexClosedRootSimplex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma convex_sixVertexClosedRootSimplex_eq
  {n : ℕ} :
-- imply
  Convex ℝ {p : Fin n → ℝ | SixVertexClosedRootSimplex p} := by
-- proof
  apply StatMech.FrontierD.convex_sixVertexClosedRootSimplex n

/--
[isClosed_sixVertexClosedRootSimplex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma isClosed_sixVertexClosedRootSimplex_eq
  {n : ℕ} :
-- imply
  IsClosed {p : Fin n → ℝ | SixVertexClosedRootSimplex p} := by
-- proof
  apply StatMech.FrontierD.isClosed_sixVertexClosedRootSimplex n

/--
[isCompact_sixVertexClosedRootSimplex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma isCompact_sixVertexClosedRootSimplex_eq
  {n : ℕ} :
-- imply
  IsCompact {p : Fin n → ℝ | SixVertexClosedRootSimplex p} := by
-- proof
  apply StatMech.FrontierD.isCompact_sixVertexClosedRootSimplex n

/--
[sixVertexBetheUpdate_closed_to_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexBetheUpdate_closed_to_open_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hc : 2 < c)
  (hhalf : 2 * n ≤ N)
  (hp : SixVertexClosedRootSimplex p) :
-- imply
  SixVertexOpenRootSimplex (sixVertexBetheUpdate c N n p) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheUpdate_closed_to_open hc hhalf hp

/--
[SixVertexOpenRootSimplex.toClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma toClosed_eq
  {n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hp : SixVertexOpenRootSimplex p) :
-- imply
  SixVertexClosedRootSimplex p := by
-- proof
  apply StatMech.FrontierD.SixVertexOpenRootSimplex.toClosed hp

/--
[sixVertexBetheUpdate_mapsTo_closedRootSimplex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexBetheUpdate_mapsTo_closedRootSimplex_eq
  {c : ℝ}
  {N n : ℕ}
-- given
  (hc : 2 < c)
  (hhalf : 2 * n ≤ N) :
-- imply
  Set.MapsTo (sixVertexBetheUpdate c N n) {p | SixVertexClosedRootSimplex p} {p | SixVertexClosedRootSimplex p} := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheUpdate_mapsTo_closedRootSimplex hc hhalf

/--
[sixVertexBetheUpdate_fixedPoint_mem_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexBetheUpdate_fixedPoint_mem_open_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hc : 2 < c)
  (hhalf : 2 * n ≤ N)
  (hp : SixVertexClosedRootSimplex p)
  (hfix : sixVertexBetheUpdate c N n p = p) :
-- imply
  SixVertexOpenRootSimplex p := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheUpdate_fixedPoint_mem_open hc hhalf hp hfix

/--
[sixVertexBetheUpdate_fixedPoint_is_solution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sixVertexBetheUpdate_fixedPoint_is_solution_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hN : 0 < N)
  (hfix : sixVertexBetheUpdate c N n p = p) :
-- imply
  SixVertexSatisfiesBetheEquations c N n p := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheUpdate_fixedPoint_is_solution hN hfix

/--
[sum_sixVertexTheta_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sum_sixVertexTheta_pair_eq
  {c : ℝ}
  {n : ℕ}
  {p : Fin n → ℝ} :
-- imply
  ∑ j, ∑ k, sixVertexTheta c (p j) (p k) = 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexTheta_pair c p

/--
[SixVertexSatisfiesBetheEquations.sum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma sum_eq_zero_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hN : 0 < N)
  (hp : SixVertexSatisfiesBetheEquations c N n p) :
-- imply
  ∑ j, p j = 0 := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesBetheEquations.sum_eq_zero hN hp

/--
[SixVertexSatisfiesBetheEquations.reverse_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean)
-/
@[path]
private lemma reverse_neg_eq_2
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hp : SixVertexSatisfiesBetheEquations c N n p) :
-- imply
  SixVertexSatisfiesBetheEquations c N n (fun j => -p j.rev) := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesBetheEquations.reverse_neg hp


-- created on 2026-10-23
