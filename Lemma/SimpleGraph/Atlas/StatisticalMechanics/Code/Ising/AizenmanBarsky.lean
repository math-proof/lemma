import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
open Finset SimpleGraph Set StatMech StatMech.Ising


/--
[hasDerivAt_isingWeight_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean)
-/
@[path]
private lemma hasDerivAt_isingWeight_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun β => isingWeight G β h s) (isingWeight G β h s * negHam G h s) β := by
-- proof
  apply StatMech.Ising.hasDerivAt_isingWeight_beta G β h s

/--
[hasDerivAt_num_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean)
-/
@[path]
private lemma hasDerivAt_num_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun β => ∑ s : ConfigSpace V, f s * isingWeight G β h s) (∑ s : ConfigSpace V, f s * (isingWeight G β h s * negHam G h s)) β := by
-- proof
  apply StatMech.Ising.hasDerivAt_num_beta G β h f

/--
[hasDerivAt_isingZ_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean)
-/
@[path]
private lemma hasDerivAt_isingZ_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun β => isingZ G β h) (∑ s : ConfigSpace V, isingWeight G β h s * negHam G h s) β := by
-- proof
  apply StatMech.Ising.hasDerivAt_isingZ_beta G β h

/--
[hasDerivAt_expectation_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean)
-/
@[path]
private lemma hasDerivAt_expectation_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun β => isingExpectation G β h f) (isingExpectation G β h (fun s => f s * negHam G h s) - isingExpectation G β h f * isingExpectation G β h (negHam G h)) β := by
-- proof
  apply StatMech.Ising.hasDerivAt_expectation_beta G β h f

/--
[expectation_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean)
-/
@[path]
private lemma expectation_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f g : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun s => f s + g s) = isingExpectation G β h f + isingExpectation G β h g := by
-- proof
  apply StatMech.Ising.expectation_add G β h f g

/--
[expectation_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean)
-/
@[path]
private lemma expectation_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {c : ℝ}
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun s => c * f s) = c * isingExpectation G β h f := by
-- proof
  apply StatMech.Ising.expectation_const_mul G β h c f

/--
[cov3sym_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean)
-/
@[path]
private lemma cov3sym_mk_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  cov3sym G β h o s(x, y) = isingExpectation G β h (fun s => spin s o * (spin s x * spin s y)) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x * spin s y) := by
-- proof
  apply StatMech.Ising.cov3sym_mk G β h o x y

/--
[ghsBoundSym_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean)
-/
@[path]
private lemma ghsBoundSym_mk_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y : V}
-- given
  (β h : ℝ) :
-- imply
  ghsBoundSym G β h o s(x, y) = cov2 G β h o x * onePt G β h y + cov2 G β h o y * onePt G β h x := by
-- proof
  apply StatMech.Ising.ghsBoundSym_mk G β h o x y

/--
[expectation_negHam_cov_expand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean)
-/
@[path]
private lemma expectation_negHam_cov_expand_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun s => f s * negHam G h s) - isingExpectation G β h f * isingExpectation G β h (negHam G h) = (∑ e ∈ G.edgeFinset, (isingExpectation G β h (fun s => f s * bond s e) - isingExpectation G β h f * isingExpectation G β h (fun s => bond s e))) + h * ∑ x, (isingExpectation G β h (fun s => f s * spin s x) - isingExpectation G β h f * isingExpectation G β h (fun s => spin s x)) := by
-- proof
  apply StatMech.Ising.expectation_negHam_cov_expand G β h f

/--
[deriv_magnetization_beta_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean)
-/
@[path]
private lemma deriv_magnetization_beta_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  deriv (fun β => isingExpectation G β h (fun s => spin s o)) β = bondEnergySusceptibility G β h o + h * susceptibility G β h o := by
-- proof
  apply StatMech.Ising.deriv_magnetization_beta_eq G β h o

/--
[bondEnergy_le_ghsSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean)
-/
@[path]
private lemma bondEnergy_le_ghsSum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hghs : GHSThreePointSym G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e := by
-- proof
  apply StatMech.Ising.bondEnergy_le_ghsSum G β h o hghs

/--
[aizenman_barsky_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AizenmanBarsky.lean)
-/
@[path]
private lemma aizenman_barsky_inequality_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
  {J : ℝ}
-- given
  (β h : ℝ)
  (hghs : GHSThreePointSym G β h o)
  (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
-- imply
  bondEnergySusceptibility G β h o ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o := by
-- proof
  apply StatMech.Ising.aizenman_barsky_inequality G β h o J hghs hfactor


-- created on 2026-10-23
