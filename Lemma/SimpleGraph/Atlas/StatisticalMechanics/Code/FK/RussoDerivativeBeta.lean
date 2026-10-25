import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBeta.Part4
open StatMech StatMech.FK


/--
[edgeProductW_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma edgeProductW_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1) :
-- imply
  0 < edgeProductW G pf ω := by
-- proof
  apply StatMech.FK.edgeProductW_pos G hpf hpf1 ω

/--
[fkWeightW_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma fkWeightW_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 0 < q) :
-- imply
  0 < fkWeightW G pf q ω := by
-- proof
  apply StatMech.FK.fkWeightW_pos G hpf hpf1 hq ω

/--
[fkZW_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma fkZW_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 0 < q) :
-- imply
  0 < fkZW G pf q := by
-- proof
  apply StatMech.FK.fkZW_pos G hpf hpf1 hq

/--
[fkZW_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma fkZW_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 0 < q) :
-- imply
  fkZW G pf q ≠ 0 := by
-- proof
  apply StatMech.FK.fkZW_ne_zero G hpf hpf1 hq

/--
[edgeProductWOff_update](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma edgeProductWOff_update_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {e₀ : Sym2 V}
  {t : ℝ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  edgeProductWOff G (Function.update pf e₀ t) e₀ ω = edgeProductWOff G pf e₀ ω := by
-- proof
  apply StatMech.FK.edgeProductWOff_update G pf e₀ t ω

/--
[edgeProductW_update_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma edgeProductW_update_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {e₀ : Sym2 V}
  {t : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (he : e₀ ∈ G.edgeFinset) :
-- imply
  edgeProductW G (Function.update pf e₀ t) ω = edgeProductWOff G pf e₀ ω * (if ω e₀ then t else 1 - t) := by
-- proof
  apply StatMech.FK.edgeProductW_update_factor G pf e₀ t ω he

/--
[hasDerivAt_edgeProductW_update](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma hasDerivAt_edgeProductW_update_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {e₀ : Sym2 V}
  {t : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (he : e₀ ∈ G.edgeFinset) :
-- imply
  HasDerivAt (fun t => edgeProductW G (Function.update pf e₀ t) ω) (edgeProductWOff G pf e₀ ω * (if ω e₀ then (1 : ℝ) else -1)) t := by
-- proof
  apply StatMech.FK.hasDerivAt_edgeProductW_update G pf e₀ t ω he

/--
[hasDerivAt_edgeProductW_clean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma hasDerivAt_edgeProductW_clean_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {e₀ : Sym2 V}
  {t : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (ht : 0 < t)
  (ht1 : t < 1)
  (he : e₀ ∈ G.edgeFinset) :
-- imply
  HasDerivAt (fun t => edgeProductW G (Function.update pf e₀ t) ω) (edgeProductW G (Function.update pf e₀ t) ω * ((coordR e₀ ω - t) / (t * (1 - t)))) t := by
-- proof
  apply StatMech.FK.hasDerivAt_edgeProductW_clean G ht ht1 ω he

/--
[hasDerivAt_fkWeightW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma hasDerivAt_fkWeightW_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {e₀ : Sym2 V}
  {t : ℝ}
  {q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (ht : 0 < t)
  (ht1 : t < 1)
  (he : e₀ ∈ G.edgeFinset) :
-- imply
  HasDerivAt (fun t => fkWeightW G (Function.update pf e₀ t) q ω) (fkWeightW G (Function.update pf e₀ t) q ω * ((coordR e₀ ω - t) / (t * (1 - t)))) t := by
-- proof
  apply StatMech.FK.hasDerivAt_fkWeightW G ht ht1 q ω he

/--
[fkNumerW_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma fkNumerW_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ} :
-- imply
  fkNumerW G pf q (fun _ => 1) = fkZW G pf q := by
-- proof
  apply StatMech.FK.fkNumerW_one G pf q

/--
[hasDerivAt_fkNumerW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma hasDerivAt_fkNumerW_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {e₀ : Sym2 V}
  {t : ℝ}
  {q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (ht : 0 < t)
  (ht1 : t < 1)
  (he : e₀ ∈ G.edgeFinset) :
-- imply
  HasDerivAt (fun t => fkNumerW G (Function.update pf e₀ t) q g) ((∑ ω : ConfigSpace (Sym2 V), g ω * (fkWeightW G (Function.update pf e₀ t) q ω * (coordR e₀ ω - t))) / (t * (1 - t))) t := by
-- proof
  apply StatMech.FK.hasDerivAt_fkNumerW G ht ht1 q g he

/--
[fkMeanW_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma fkMeanW_eq_div_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  fkMeanW G pf q g = fkNumerW G pf q g / fkZW G pf q := by
-- proof
  apply StatMech.FK.fkMeanW_eq_div G pf q g

/--
[fkMeanW_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma fkMeanW_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
-- given
  (g h : ConfigSpace (Sym2 V) → ℝ) :
-- imply
  fkMeanW G pf q (fun ω => g ω + h ω) = fkMeanW G pf q g + fkMeanW G pf q h := by
-- proof
  apply StatMech.FK.fkMeanW_add G pf q g h

/--
[fkMeanW_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma fkMeanW_const_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {c : ℝ}
-- given
  (hZ : fkZW G pf q ≠ 0) :
-- imply
  fkMeanW G pf q (fun _ => c) = c := by
-- proof
  apply StatMech.FK.fkMeanW_const G pf q hZ

/--
[fkMeanW_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma fkMeanW_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {c : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  fkMeanW G pf q (fun ω => c * g ω) = c * fkMeanW G pf q g := by
-- proof
  apply StatMech.FK.fkMeanW_const_mul G pf q c g

/--
[fkCovW_sub_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma fkCovW_sub_const_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {f g : ConfigSpace (Sym2 V) → ℝ}
  {c : ℝ}
-- given
  (hZ : fkZW G pf q ≠ 0) :
-- imply
  fkCovW G pf q f (fun ω => g ω - c) = fkCovW G pf q f g := by
-- proof
  apply StatMech.FK.fkCovW_sub_const G pf q f g hZ

/--
[hasDerivAt_fkMeanW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma hasDerivAt_fkMeanW_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {e₀ : Sym2 V}
  {g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 0 < q)
  (he : e₀ ∈ G.edgeFinset) :
-- imply
  HasDerivAt (fun t => fkMeanW G (Function.update pf e₀ t) q g) (fkCovW G (Function.update pf e₀ (pf e₀)) q g (coordR e₀) / (pf e₀ * (1 - pf e₀))) (pf e₀) := by
-- proof
  apply StatMech.FK.hasDerivAt_fkMeanW G hpf hpf1 hq he g

/--
[deriv_fkMeanW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma deriv_fkMeanW_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {e₀ : Sym2 V}
  {g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 0 < q)
  (he : e₀ ∈ G.edgeFinset) :
-- imply
  deriv (fun t => fkMeanW G (Function.update pf e₀ t) q g) (pf e₀) = fkCovW G (Function.update pf e₀ (pf e₀)) q g (coordR e₀) / (pf e₀ * (1 - pf e₀)) := by
-- proof
  apply StatMech.FK.deriv_fkMeanW G hpf hpf1 hq he g

/--
[hasDerivAt_fkProbWOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma hasDerivAt_fkProbWOf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {e₀ : Sym2 V}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 0 < q)
  (he : e₀ ∈ G.edgeFinset) :
-- imply
  HasDerivAt (fun t => fkProbWOf G (Function.update pf e₀ t) q A) (fkCovW G (Function.update pf e₀ (pf e₀)) q (A.indicator (fun _ => (1 : ℝ))) (coordR e₀) / (pf e₀ * (1 - pf e₀))) (pf e₀) := by
-- proof
  apply StatMech.FK.hasDerivAt_fkProbWOf G hpf hpf1 hq he A

/--
[deriv_fkProbWOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma deriv_fkProbWOf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {e₀ : Sym2 V}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 0 < q)
  (he : e₀ ∈ G.edgeFinset) :
-- imply
  deriv (fun t => fkProbWOf G (Function.update pf e₀ t) q A) (pf e₀) = fkCovW G (Function.update pf e₀ (pf e₀)) q (A.indicator (fun _ => (1 : ℝ))) (coordR e₀) / (pf e₀ * (1 - pf e₀)) := by
-- proof
  apply StatMech.FK.deriv_fkProbWOf G hpf hpf1 hq he A

/--
[hasDerivAt_paramOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma hasDerivAt_paramOfBeta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J β : ℝ} :
-- imply
  HasDerivAt (fun b => 1 - Real.exp (-(b * J))) (J * Real.exp (-(β * J))) β := by
-- proof
  apply StatMech.FK.hasDerivAt_paramOfBeta G J β

/--
[hasDerivAt_fkProbWOf_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivativeBeta.lean)
-/
@[path]
private lemma hasDerivAt_fkProbWOf_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {e₀ : Sym2 V}
  {A : Set (ConfigSpace (Sym2 V))}
  {J β₀ : ℝ}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 0 < q)
  (he : e₀ ∈ G.edgeFinset)
  (hpt : pf e₀ = 1 - Real.exp (-(β₀ * J))) :
-- imply
  HasDerivAt (fun b => fkProbWOf G (Function.update pf e₀ (1 - Real.exp (-(b * J)))) q A) ((J / (1 - Real.exp (-(β₀ * J)))) * fkCovW G (Function.update pf e₀ (pf e₀)) q (A.indicator (fun _ => (1 : ℝ))) (coordR e₀)) β₀ := by
-- proof
  apply StatMech.FK.hasDerivAt_fkProbWOf_beta G hpf hpf1 hq he A J β₀ hpt


-- created on 2026-10-23
