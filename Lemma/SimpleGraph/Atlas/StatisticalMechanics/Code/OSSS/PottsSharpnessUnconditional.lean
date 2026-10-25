import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.PottsSharpnessUnconditional
open MeasureTheory Filter StatMech StatMech.OSSS StatMech.OSSS.PottsSharpnessUnconditional


/--
[wiredFinite_boxBoundary_mass_eq_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PottsSharpnessUnconditional.lean)
-/
@[path]
private lemma wiredFinite_boxBoundary_mass_eq_conn_eq
  {d m q : Nat}
  [NeZero q]
  {beta : Real}
-- given
  (hm : 1 <= m)
  (hbeta : 0 < beta) :
-- imply
  (wiredFiniteMeasure d m (by have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0) linarith : 0 < 1 - Real.exp (-beta)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : Real) < q) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d m) = wiredConnToBdryProbQ (boxGraph d m) (boxBoundary d m) q (1 - Real.exp (-beta)) (boxOrigin d m) := by
-- proof
  apply StatMech.OSSS.PottsSharpnessUnconditional.wiredFinite_boxBoundary_mass_eq_conn d m q hm beta hbeta

/--
[exists_supercritical_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PottsSharpnessUnconditional.lean)
-/
@[path]
private lemma exists_supercritical_beta_eq
  {d q : Nat}
  [NeZero q]
-- given
  (hd : 2 <= d)
  (hq : 2 <= q) :
-- imply
  ∃ beta0 : Real, 0 < betaFKThetaQ d q (by exact_mod_cast (show (1 : Nat) <= q by omega) : (1 : Real) <= q) beta0 := by
-- proof
  apply StatMech.OSSS.PottsSharpnessUnconditional.exists_supercritical_beta d q hd hq

/--
[potts_boundary_bias_decay_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PottsSharpnessUnconditional.lean)
-/
@[path]
private lemma potts_boundary_bias_decay_even_eq
  {d q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta : Real}
-- given
  (hd : 2 <= d)
  (hq : 2 <= q)
  (hbeta : 0 < beta)
  (hcrit : beta < fkBetaCriticalQ d q) :
-- imply
  ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n → 0 <= pottsBoundaryProbWired (boxGraph d (2 * n)) (boxBoundary d (2 * n)) q b beta 1 (boxOrigin d (2 * n)) - 1 / (q : Real) ∧ pottsBoundaryProbWired (boxGraph d (2 * n)) (boxBoundary d (2 * n)) q b beta 1 (boxOrigin d (2 * n)) - 1 / (q : Real) <= Real.exp (-((n : Real) / Q)) := by
-- proof
  apply StatMech.OSSS.PottsSharpnessUnconditional.potts_boundary_bias_decay_even d q hd hq b beta hbeta hcrit

/--
[potts_boundary_bias_eq_wired_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PottsSharpnessUnconditional.lean)
-/
@[path]
private lemma potts_boundary_bias_eq_wired_mass_eq
  {d m q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta : Real}
-- given
  (hd : 1 <= d)
  (hm : 1 <= m)
  (hq : 2 <= q)
  (hbeta : 0 < beta) :
-- imply
  pottsBoundaryProbWired (boxGraph d m) (boxBoundary d m) q b beta 1 (boxOrigin d m) - 1 / (q : Real) = ((q : Real) - 1) / q * (wiredFiniteMeasure d m (by have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0) linarith : 0 < 1 - Real.exp (-beta)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d m) := by
-- proof
  apply StatMech.OSSS.PottsSharpnessUnconditional.potts_boundary_bias_eq_wired_mass d m q hd hm hq b beta hbeta

/--
[potts_boundary_bias_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PottsSharpnessUnconditional.lean)
-/
@[path]
private lemma potts_boundary_bias_decay_eq
  {d q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta : Real}
-- given
  (hd : 2 <= d)
  (hq : 2 <= q)
  (hbeta : 0 < beta)
  (hcrit : beta < fkBetaCriticalQ d q) :
-- imply
  ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n → 0 <= pottsBoundaryProbWired (boxGraph d n) (boxBoundary d n) q b beta 1 (boxOrigin d n) - 1 / (q : Real) ∧ pottsBoundaryProbWired (boxGraph d n) (boxBoundary d n) q b beta 1 (boxOrigin d n) - 1 / (q : Real) <= Real.exp (-((n : Real) / Q)) := by
-- proof
  apply StatMech.OSSS.PottsSharpnessUnconditional.potts_boundary_bias_decay d q hd hq b beta hbeta hcrit


-- created on 2026-10-23
