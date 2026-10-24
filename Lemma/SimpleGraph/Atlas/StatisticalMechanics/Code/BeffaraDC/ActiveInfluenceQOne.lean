import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.ActiveInfluenceQOne
open Finset Set StatMech StatMech.BeffaraDC


/--
[activeWeight_one_eq_osssWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluenceQOne.lean)
-/
@[path]
private lemma activeWeight_one_eq_osssWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {ω : ConfigSpace G.edgeSet} :
-- imply
  activeWeight G (fun _ => p) 1 ω = OSSS.weight (OSSS.bernoulliWeight p) ω := by
-- proof
  apply StatMech.BeffaraDC.activeWeight_one_eq_osssWeight G p ω

/--
[activeZ_one_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluenceQOne.lean)
-/
@[path]
private lemma activeZ_one_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  activeZ G (fun _ => p) 1 = 1 := by
-- proof
  apply StatMech.BeffaraDC.activeZ_one_eq_one G hp0 hp1

/--
[activeProb_one_eq_osssWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluenceQOne.lean)
-/
@[path]
private lemma activeProb_one_eq_osssWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {ω : ConfigSpace G.edgeSet}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  activeProb G (fun _ => p) 1 ω = OSSS.weight (OSSS.bernoulliWeight p) ω := by
-- proof
  apply StatMech.BeffaraDC.activeProb_one_eq_osssWeight G hp0 hp1 ω

/--
[activeMean_one_eq_osssExpect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluenceQOne.lean)
-/
@[path]
private lemma activeMean_one_eq_osssExpect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {f : ConfigSpace G.edgeSet → ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  activeMean G (fun _ => p) 1 f = OSSS.expect (OSSS.bernoulliWeight p) f := by
-- proof
  apply StatMech.BeffaraDC.activeMean_one_eq_osssExpect G hp0 hp1 f

/--
[activeCov_one_eq_osssCov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluenceQOne.lean)
-/
@[path]
private lemma activeCov_one_eq_osssCov_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {f g : ConfigSpace G.edgeSet → ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  activeCov G (fun _ => p) 1 f g = OSSS.cov (OSSS.bernoulliWeight p) f g := by
-- proof
  apply StatMech.BeffaraDC.activeCov_one_eq_osssCov G hp0 hp1 f g

/--
[activeProbOf_one_eq_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluenceQOne.lean)
-/
@[path]
private lemma activeProbOf_one_eq_prob_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {A : Set (ConfigSpace G.edgeSet)}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  activeProbOf G (fun _ => p) 1 A = StatMech.prob p A := by
-- proof
  apply StatMech.BeffaraDC.activeProbOf_one_eq_prob G hp0 hp1 A

/--
[active_openMarginal_one_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluenceQOne.lean)
-/
@[path]
private lemma active_openMarginal_one_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {e : G.edgeSet}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  openMarginal (activeProb G (fun _ => p) 1) e = p := by
-- proof
  apply StatMech.BeffaraDC.active_openMarginal_one_eq G hp hp1 e

/--
[activeInfluence_one_eq_infl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluenceQOne.lean)
-/
@[path]
private lemma activeInfluence_one_eq_infl_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {A : Set (ConfigSpace G.edgeSet)}
  {e : G.edgeSet}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hA : IsIncreasing A) :
-- imply
  activeInfluence G p 1 A e = OSSS.infl (OSSS.bernoulliWeight p) (A.indicator fun _ => (1 : ℝ)) e := by
-- proof
  apply StatMech.BeffaraDC.activeInfluence_one_eq_infl G hp hp1 A hA e

/--
[activeInfluence_one_eq_influence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluenceQOne.lean)
-/
@[path]
private lemma activeInfluence_one_eq_influence_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {A : Set (ConfigSpace G.edgeSet)}
  {e : G.edgeSet}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hA : IsIncreasing A) :
-- imply
  activeInfluence G p 1 A e = influence p A e := by
-- proof
  apply StatMech.BeffaraDC.activeInfluence_one_eq_influence G hp hp1 A hA e

/--
[maxActiveInfluence_qOne_corrected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluenceQOne.lean)
-/
@[path]
private lemma maxActiveInfluence_qOne_corrected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Nonempty G.edgeSet]
  {p : ℝ}
  {A : Set (ConfigSpace G.edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hA : IsIncreasing A) :
-- imply
  ∃ e : G.edgeSet, activeProbOf G (fun _ => p) 1 A * (1 - activeProbOf G (fun _ => p) 1 A) * Real.log (Fintype.card G.edgeSet : ℝ) / (Fintype.card G.edgeSet : ℝ) / (1 + pBiasedCorrection p * Real.log (Fintype.card G.edgeSet : ℝ)) ≤ activeInfluence G p 1 A e := by
-- proof
  apply StatMech.BeffaraDC.maxActiveInfluence_qOne_corrected G hp hp1 A hA

/--
[maxActiveInfluence_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluenceQOne.lean)
-/
@[path]
private lemma maxActiveInfluence_half_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Nonempty G.edgeSet]
  {A : Set (ConfigSpace G.edgeSet)}
-- given
  (hA : IsIncreasing A) :
-- imply
  ∃ e : G.edgeSet, activeProbOf G (fun _ => (1 / 2 : ℝ)) 1 A * (1 - activeProbOf G (fun _ => (1 / 2 : ℝ)) 1 A) * Real.log (Fintype.card G.edgeSet : ℝ) / (Fintype.card G.edgeSet : ℝ) ≤ activeInfluence G (1 / 2 : ℝ) 1 A e := by
-- proof
  apply StatMech.BeffaraDC.maxActiveInfluence_half G A hA

/--
[maxActiveInfluence_qOne_compactWindow_of_bkkkl_u0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluenceQOne.lean)
-/
@[path]
private lemma maxActiveInfluence_qOne_compactWindow_of_bkkkl_u0_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {W : Type}
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  [Nonempty H.edgeSet]
  {ε p : ℝ}
  {Hpb : StatMech.Probability.kpb_PBiasedHC (1 - ε / 2)}
  {A : Set (ConfigSpace H.edgeSet)}
-- given
  (hε0 : 0 < ε)
  (hp : p ∈ Set.Icc ε (1 - ε))
  (hA : IsIncreasing A) :
-- imply
  ∃ e : H.edgeSet, activeProbOf H (fun _ => p) 1 A * (1 - activeProbOf H (fun _ => p) 1 A) * Real.log (Fintype.card H.edgeSet : ℝ) / (Fintype.card H.edgeSet : ℝ) ≤ activeInfluence H p 1 A e := by
-- proof
  apply StatMech.BeffaraDC.maxActiveInfluence_qOne_compactWindow_of_bkkkl_u0 G H hε0 hp Hpb A hA


-- created on 2026-10-23
