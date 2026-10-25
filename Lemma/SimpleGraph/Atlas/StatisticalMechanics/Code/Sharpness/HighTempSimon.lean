import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part8
open Finset SimpleGraph StatMech StatMech.Sharpness


/--
[mem_highTempInternalEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma mem_highTempInternalEdges_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {e : Sym2 V} :
-- imply
  e ∈ highTempInternalEdges G S ↔ e ∈ G.edgeFinset ∧ edgeInside S e := by
-- proof
  apply StatMech.Sharpness.mem_highTempInternalEdges G S e

/--
[highTempInput_symmDiff_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma highTempInput_symmDiff_subset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {o z : V}
  {p : HighTempSwitchInput (V := V)}
-- given
  (hp : p.Valid G S o z) :
-- imply
  p.F ∆ p.H ⊆ G.edgeFinset := by
-- proof
  apply StatMech.Sharpness.highTempInput_symmDiff_subset G hp

/--
[highTempInput_symmDiff_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma highTempInput_symmDiff_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {o z : V}
  {p : HighTempSwitchInput (V := V)}
-- given
  (hp : p.Valid G S o z) :
-- imply
  HasOddBoundary (p.F ∆ p.H) (sourcePair o z) := by
-- proof
  apply StatMech.Sharpness.highTempInput_symmDiff_sources G hp

/--
[highTempSwitch_mem_outputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma highTempSwitch_mem_outputs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {o z : V}
-- given
  (ho : o ∈ S)
  (hz : z ∉ S)
  (p : HighTempSwitchInput (V := V))
  (hp : p ∈ highTempSwitchInputs G S o z) :
-- imply
  highTempSwitch G S o z ho hz p (by simpa [highTempSwitchInputs] using hp) ∈ highTempSwitchOutputs G S o z := by
-- proof
  apply StatMech.Sharpness.highTempSwitch_mem_outputs G S o z ho hz p hp

/--
[highTempSwitch_recover_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma highTempSwitch_recover_symmDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F H Q : Finset (Sym2 V)}
  {e : Sym2 V}
-- given
  (heF : e ∈ F)
  (heQ : e ∉ Q) :
-- imply
  insert e ((F ∆ Q).erase e) ∆ (H ∆ Q) = F ∆ H := by
-- proof
  apply StatMech.Sharpness.highTempSwitch_recover_symmDiff G F H Q heF heQ

/--
[highTempSwitch_recover_F](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma highTempSwitch_recover_F_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {F Q : Finset (Sym2 V)}
  {e : Sym2 V}
-- given
  (heF : e ∈ F)
  (heQ : e ∉ Q) :
-- imply
  insert e ((F ∆ Q).erase e) ∆ Q = F := by
-- proof
  apply StatMech.Sharpness.highTempSwitch_recover_F G F Q heF heQ

/--
[highTempSwitch_recover_H](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma highTempSwitch_recover_H_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H Q : Finset (Sym2 V)} :
-- imply
  (H ∆ Q) ∆ Q = H := by
-- proof
  apply StatMech.Sharpness.highTempSwitch_recover_H G H Q

/--
[highTempSwitchMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma highTempSwitchMap_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {o z : V}
-- given
  (ho : o ∈ S)
  (hz : z ∉ S) :
-- imply
  Function.Injective (highTempSwitchMap G S o z ho hz) := by
-- proof
  apply StatMech.Sharpness.highTempSwitchMap_injective G S o z ho hz

/--
[highTempSwitch_weight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma highTempSwitch_weight_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {t : Sym2 V → ℝ}
  {S : Finset V}
  {o z : V}
-- given
  (ho : o ∈ S)
  (hz : z ∉ S)
  (p : HighTempSwitchInput (V := V))
  (hp : p.Valid G S o z) :
-- imply
  highTempSwitchOutputWeight t (highTempSwitch G S o z ho hz p hp) = highTempSwitchInputWeight t p := by
-- proof
  apply StatMech.Sharpness.highTempSwitch_weight_eq G t S o z ho hz p hp

/--
[highTempSwitch_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma highTempSwitch_sum_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {t : Sym2 V → ℝ}
  {S : Finset V}
  {o z : V}
-- given
  (ht : ∀ e, 0 ≤ t e)
  (ho : o ∈ S)
  (hz : z ∉ S) :
-- imply
  (∑ p : ↥(highTempSwitchInputs G S o z), highTempSwitchInputWeight t p.1) ≤ ∑ r : ↥(highTempSwitchOutputs G S o z), highTempSwitchOutputWeight t r.1 := by
-- proof
  apply StatMech.Sharpness.highTempSwitch_sum_le G t ht S o z ho hz

/--
[highTempSwitch_input_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma highTempSwitch_input_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {t : Sym2 V → ℝ}
  {S : Finset V}
  {o z : V} :
-- imply
  (∑ p : ↥(highTempSwitchInputs G S o z), highTempSwitchInputWeight t p.1) = highTempSourceSum G.edgeFinset t (sourcePair o z) * highTempSourceSum (highTempInternalEdges G S) t ∅ := by
-- proof
  apply StatMech.Sharpness.highTempSwitch_input_sum G t S o z

/--
[highTempSwitch_output_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma highTempSwitch_output_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {t : Sym2 V → ℝ}
  {S : Finset V}
  {o z : V} :
-- imply
  (∑ r : ↥(highTempSwitchOutputs G S o z), highTempSwitchOutputWeight t r.1) = ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S), t s(x, y) * highTempSourceSum (highTempInternalEdges G S) t (sourcePair o x) * highTempSourceSum G.edgeFinset t (sourcePair y z) := by
-- proof
  apply StatMech.Sharpness.highTempSwitch_output_sum G t S o z

/--
[highTemp_sourceSum_simon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma highTemp_sourceSum_simon_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {t : Sym2 V → ℝ}
  {S : Finset V}
  {o z : V}
-- given
  (ht : ∀ e, 0 ≤ t e)
  (ho : o ∈ S)
  (hz : z ∉ S) :
-- imply
  highTempSourceSum G.edgeFinset t (sourcePair o z) * highTempSourceSum (highTempInternalEdges G S) t ∅ ≤ ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S), t s(x, y) * highTempSourceSum (highTempInternalEdges G S) t (sourcePair o x) * highTempSourceSum G.edgeFinset t (sourcePair y z) := by
-- proof
  apply StatMech.Sharpness.highTemp_sourceSum_simon G t ht S o z ho hz

/--
[highTempSourceSum_zero_extension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma highTempSourceSum_zero_extension_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {I E : Finset (Sym2 V)}
  {t t' : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hIE : I ⊆ E)
  (hin : ∀ e ∈ I, t' e = t e)
  (hout : ∀ e ∈ E, e ∉ I → t' e = 0) :
-- imply
  highTempSourceSum E t' A = highTempSourceSum I t A := by
-- proof
  apply StatMech.Sharpness.highTempSourceSum_zero_extension G I E hIE t t' hin hout A

/--
[highTempSourceSum_couplingIn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma highTempSourceSum_couplingIn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {S A : Finset V} :
-- imply
  highTempSourceSum G.edgeFinset (fun e => Real.tanh (beta * couplingIn J S e)) A = highTempSourceSum (highTempInternalEdges G S) (fun e => Real.tanh (beta * J e)) A := by
-- proof
  apply StatMech.Sharpness.highTempSourceSum_couplingIn G beta J S A

/--
[twoPointJ_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma twoPointJ_self_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {a : V} :
-- imply
  twoPointJ G beta J a a = 1 := by
-- proof
  apply StatMech.Sharpness.twoPointJ_self G beta J a

/--
[twoPointJ_high_temp_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma twoPointJ_high_temp_ratio_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {a b : V} :
-- imply
  twoPointJ G beta J a b = highTempSourceSum G.edgeFinset (fun e => Real.tanh (beta * J e)) (sourcePair a b) / highTempSourceSum G.edgeFinset (fun e => Real.tanh (beta * J e)) ∅ := by
-- proof
  apply StatMech.Sharpness.twoPointJ_high_temp_ratio G beta J a b

/--
[highTempSourceSum_empty_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma highTempSourceSum_empty_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {E : Finset (Sym2 V)}
  {t : Sym2 V → ℝ}
-- given
  (ht : ∀ e ∈ E, 0 ≤ t e) :
-- imply
  0 < highTempSourceSum E t ∅ := by
-- proof
  apply StatMech.Sharpness.highTempSourceSum_empty_pos G E t ht

/--
[twoPointJ_couplingIn_high_temp_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma twoPointJ_couplingIn_high_temp_ratio_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {a b : V} :
-- imply
  twoPointJ G beta (couplingIn J S) a b = highTempSourceSum (highTempInternalEdges G S) (fun e => Real.tanh (beta * J e)) (sourcePair a b) / highTempSourceSum (highTempInternalEdges G S) (fun e => Real.tanh (beta * J e)) ∅ := by
-- proof
  apply StatMech.Sharpness.twoPointJ_couplingIn_high_temp_ratio G beta J S a b

/--
[twoPointJ_simon_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma twoPointJ_simon_finite_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {o z : V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (ho : o ∈ S)
  (hz : z ∉ S) :
-- imply
  twoPointJ G beta J o z ≤ ∑ x ∈ S, ∑ y ∈ (Finset.univ \ S), Real.tanh (beta * J s(x, y)) * twoPointJ G beta (couplingIn J S) o x * twoPointJ G beta J y z := by
-- proof
  apply StatMech.Sharpness.twoPointJ_simon_finite G beta J hbeta hJ S o z ho hz

/--
[twoPointJ_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma twoPointJ_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {a b : V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ twoPointJ G beta J a b := by
-- proof
  apply StatMech.Sharpness.twoPointJ_nonneg G beta J hbeta hJ a b

/--
[twoPointJ_simonLieb_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean)
-/
@[path]
private lemma twoPointJ_simonLieb_finite_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {o : V}
-- given
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (ho : o ∈ S) :
-- imply
  SimonLieb (twoPointJ G beta J) o S (simonWeightPair G beta J S o) (Finset.univ \ S) := by
-- proof
  apply StatMech.Sharpness.twoPointJ_simonLieb_finite G beta J hbeta hJ S o ho


-- created on 2026-10-23
