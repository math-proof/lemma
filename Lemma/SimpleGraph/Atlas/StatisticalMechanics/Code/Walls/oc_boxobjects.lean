import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc_boxobjects.Part2
open Finset Set StatMech StatMech.Walls


/--
[oc_theta_eq_fkProbOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_theta_eq_fkProbOf_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {n : ℕ}
  {β : ℝ} :
-- imply
  oc_theta Gf Af n β = fkProbOf (Gf n) β 2 (Af n) := by
-- proof
  apply StatMech.Walls.oc_theta_eq_fkProbOf Gf Af n β

/--
[oc_S_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_S_zero_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {β : ℝ} :
-- imply
  oc_S Gf Af 0 β = 0 := by
-- proof
  apply StatMech.Walls.oc_S_zero Gf Af β

/--
[oc_S_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_S_succ_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {n : ℕ}
  {β : ℝ} :
-- imply
  oc_S Gf Af (n + 1) β = oc_S Gf Af n β + oc_theta Gf Af n β := by
-- proof
  apply StatMech.Walls.oc_S_succ Gf Af n β

/--
[oc_theta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_theta_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 < β)
  (hβ1 : β < 1) :
-- imply
  0 ≤ oc_theta Gf Af n β := by
-- proof
  apply StatMech.Walls.oc_theta_nonneg Gf Af hβ hβ1 n

/--
[oc_theta_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_theta_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 < β)
  (hβ1 : β < 1) :
-- imply
  oc_theta Gf Af n β ≤ 1 := by
-- proof
  apply StatMech.Walls.oc_theta_le_one Gf Af hβ hβ1 n

/--
[oc_theta_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_theta_mem_Icc_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 < β)
  (hβ1 : β < 1) :
-- imply
  oc_theta Gf Af n β ∈ Set.Icc (0 : ℝ) 1 := by
-- proof
  apply StatMech.Walls.oc_theta_mem_Icc Gf Af hβ hβ1 n

/--
[oc_indicator_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_indicator_idem_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  ((Af n).indicator (fun _ => (1 : ℝ)) ω) * ((Af n).indicator (fun _ => (1 : ℝ)) ω) = (Af n).indicator (fun _ => (1 : ℝ)) ω := by
-- proof
  apply StatMech.Walls.oc_indicator_idem Gf Af n ω

/--
[oc_indicator_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_indicator_zero_or_one_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  (Af n).indicator (fun _ => (1 : ℝ)) ω = 0 ∨ (Af n).indicator (fun _ => (1 : ℝ)) ω = 1 := by
-- proof
  apply StatMech.Walls.oc_indicator_zero_or_one Gf Af n ω

/--
[oc_S_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_S_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 < β)
  (hβ1 : β < 1) :
-- imply
  0 ≤ oc_S Gf Af n β := by
-- proof
  apply StatMech.Walls.oc_S_nonneg Gf Af hβ hβ1 n

/--
[oc_S_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_S_le_card_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 < β)
  (hβ1 : β < 1) :
-- imply
  oc_S Gf Af n β ≤ (n : ℝ) := by
-- proof
  apply StatMech.Walls.oc_S_le_card Gf Af hβ hβ1 n

/--
[oc_hasDerivAt_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_hasDerivAt_theta_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 < β)
  (hβ1 : β < 1) :
-- imply
  HasDerivAt (fun b => oc_theta Gf Af n b) ((∑ e ∈ (Gf n).edgeFinset, fkCov (Gf n) β 2 ((Af n).indicator (fun _ => (1 : ℝ))) (coord e)) / (β * (1 - β))) β := by
-- proof
  apply StatMech.Walls.oc_hasDerivAt_theta Gf Af hβ hβ1 n

/--
[oc_hasDerivAt_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_hasDerivAt_S_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 < β)
  (hβ1 : β < 1) :
-- imply
  HasDerivAt (fun b => oc_S Gf Af n b) (∑ k ∈ Finset.range n, (∑ e ∈ (Gf k).edgeFinset, fkCov (Gf k) β 2 ((Af k).indicator (fun _ => (1 : ℝ))) (coord e)) / (β * (1 - β))) β := by
-- proof
  apply StatMech.Walls.oc_hasDerivAt_S Gf Af hβ hβ1 n

/--
[oc_differentiableAt_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_differentiableAt_theta_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 < β)
  (hβ1 : β < 1) :
-- imply
  DifferentiableAt ℝ (fun b => oc_theta Gf Af n b) β := by
-- proof
  apply StatMech.Walls.oc_differentiableAt_theta Gf Af hβ hβ1 n

/--
[oc_theta_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_theta_mono_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {n : ℕ}
  {β₁ β₂ : ℝ}
-- given
  (hAf : ∀ n, IsIncreasing (Af n))
  (hβ₁ : 0 < β₁)
  (hβ₂1 : β₂ < 1)
  (hle : β₁ ≤ β₂) :
-- imply
  oc_theta Gf Af n β₁ ≤ oc_theta Gf Af n β₂ := by
-- proof
  apply StatMech.Walls.oc_theta_mono Gf Af hAf n hβ₁ hβ₂1 hle

/--
[oc_S_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_S_mono_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {n : ℕ}
  {β₁ β₂ : ℝ}
-- given
  (hAf : ∀ n, IsIncreasing (Af n))
  (hβ₁ : 0 < β₁)
  (hβ₂1 : β₂ < 1)
  (hle : β₁ ≤ β₂) :
-- imply
  oc_S Gf Af n β₁ ≤ oc_S Gf Af n β₂ := by
-- proof
  apply StatMech.Walls.oc_S_mono Gf Af hAf n hβ₁ hβ₂1 hle

/--
[oc_S_mono_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_S_mono_scale_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {β : ℝ}
-- given
  (hβ : 0 < β)
  (hβ1 : β < 1) :
-- imply
  Monotone (fun n => oc_S Gf Af n β) := by
-- proof
  apply StatMech.Walls.oc_S_mono_scale Gf Af hβ hβ1

/--
[oc_boxFamily_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_boxFamily_theta_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {n : ℕ}
  {β : ℝ}
-- given
  (hAf : ∀ n, IsIncreasing (Af n)) :
-- imply
  (oc_boxFamily Gf Af hAf).theta n β = oc_theta Gf Af n β := by
-- proof
  apply StatMech.Walls.oc_boxFamily_theta Gf Af hAf n β

/--
[oc_boxFamily_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_boxFamily_S_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {n : ℕ}
  {β : ℝ}
-- given
  (hAf : ∀ n, IsIncreasing (Af n)) :
-- imply
  (oc_boxFamily Gf Af hAf).S n β = oc_S Gf Af n β := by
-- proof
  apply StatMech.Walls.oc_boxFamily_S Gf Af hAf n β

/--
[oc_boxFamily_S_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_boxFamily_S_eq_sum_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {n : ℕ}
  {β : ℝ}
-- given
  (hAf : ∀ n, IsIncreasing (Af n)) :
-- imply
  (oc_boxFamily Gf Af hAf).S n β = ∑ k ∈ Finset.range n, (oc_boxFamily Gf Af hAf).theta k β := by
-- proof
  apply StatMech.Walls.oc_boxFamily_S_eq_sum Gf Af hAf n β

/--
[oc_boxFamily_theta_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_boxFamily_theta_mem_Icc_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {β : ℝ}
  {n : ℕ}
-- given
  (hAf : ∀ n, IsIncreasing (Af n))
  (hβ : 0 < β)
  (hβ1 : β < 1) :
-- imply
  (oc_boxFamily Gf Af hAf).theta n β ∈ Set.Icc (0 : ℝ) 1 := by
-- proof
  apply StatMech.Walls.oc_boxFamily_theta_mem_Icc Gf Af hAf hβ hβ1 n

/--
[oc_boxFamily_theta_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxobjects.lean)
-/
@[path]
private lemma oc_boxFamily_theta_mono_eq
  [Fintype V]
  [DecidableEq V]
  {Gf : ℕ → SimpleGraph V}
  [∀ n, DecidableRel (Gf n).Adj]
  {Af : ℕ → Set (ConfigSpace (Sym2 V))}
  {n : ℕ}
  {β₁ β₂ : ℝ}
-- given
  (hAf : ∀ n, IsIncreasing (Af n))
  (hβ₁ : 0 < β₁)
  (hβ₂1 : β₂ < 1)
  (hle : β₁ ≤ β₂) :
-- imply
  (oc_boxFamily Gf Af hAf).theta n β₁ ≤ (oc_boxFamily Gf Af hAf).theta n β₂ := by
-- proof
  apply StatMech.Walls.oc_boxFamily_theta_mono Gf Af hAf n hβ₁ hβ₂1 hle


-- created on 2026-10-23
