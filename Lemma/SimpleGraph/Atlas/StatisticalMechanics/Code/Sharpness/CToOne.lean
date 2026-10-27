import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.CToOne.Part3
open Filter Topology StatMech StatMech.Sharpness


/--
[sct_translate_box_subset_double](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean)
-/
@[path]
private lemma sct_translate_box_subset_double_eq
  {d n : ℕ}
  {y : Site d}
-- given
  (hy : y ∈ box d n) :
-- imply
  (fun z : Site d => z - y) '' box d n ⊆ box d (2 * n) := by
-- proof
  apply StatMech.Sharpness.sct_translate_box_subset_double hy

/--
[sct_expectation_spin_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean)
-/
@[path]
private lemma sct_expectation_spin_lt_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun s => spin s x) < 1 := by
-- proof
  apply StatMech.Sharpness.sct_expectation_spin_lt_one G β h x

/--
[sct_deriv_magnetization_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean)
-/
@[path]
private lemma sct_deriv_magnetization_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 < β)
  (hh : 0 ≤ h) :
-- imply
  0 < deriv (fun t => isingExpectation G β t (fun s => spin s o)) h := by
-- proof
  apply StatMech.Sharpness.sct_deriv_magnetization_pos G β h hβ hh o

/--
[sct_expectation_spin_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean)
-/
@[path]
private lemma sct_expectation_spin_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 < β)
  (hh : 0 < h) :
-- imply
  0 < isingExpectation G β h (fun s => spin s o) := by
-- proof
  apply StatMech.Sharpness.sct_expectation_spin_pos G β h hβ hh o

/--
[sct_box_from_griffiths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean)
-/
@[path]
private lemma sct_box_from_griffiths_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {E₁ E₂ : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {z : V}
-- given
  (hf : V → ℝ)
  (hsub : E₁ ⊆ E₂)
  (hJ : ∀ e ∈ E₂, 0 ≤ J e)
  (hhf : ∀ x, 0 ≤ hf x)
  (hdiag : ∀ e ∈ E₂, e ∉ E₁ → ¬ e.IsDiag) :
-- imply
  expJ E₁ J hf (spinProd {z}) ≤ expJ E₂ J hf (spinProd {z}) := by
-- proof
  apply StatMech.Sharpness.sct_box_from_griffiths G E₁ E₂ J hf hsub hJ hhf hdiag z

/--
[sct_ratio_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean)
-/
@[path]
private lemma sct_ratio_lower_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b M : ℝ}
-- given
  (ha : 0 < a)
  (hM : a ≤ M)
  (hc : 0 ≤ b) :
-- imply
  b / M ≤ b / a := by
-- proof
  apply StatMech.Sharpness.sct_ratio_lower G ha hM hc

/--
[sct_ratioSeq_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean)
-/
@[path]
private lemma sct_ratioSeq_tendsto_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : ℕ → ℝ}
  {L : ℝ}
-- given
  (hLpos : 0 < L)
  (hM : Tendsto M atTop (𝓝 L)) :
-- imply
  Tendsto (fun n : ℕ => M n / M (2 * n)) atTop (𝓝 1) := by
-- proof
  apply StatMech.Sharpness.sct_ratioSeq_tendsto_one G M hLpos hM

/--
[sct_c_to_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean)
-/
@[path]
private lemma sct_c_to_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M c : ℕ → ℝ}
  {L : ℝ}
-- given
  (hLpos : 0 < L)
  (hM : Tendsto M atTop (𝓝 L))
  (hsqueeze : ∀ n, M n / M (2 * n) ≤ c n)
  (hle_one : ∀ n, c n ≤ 1) :
-- imply
  Tendsto c atTop (𝓝 1) := by
-- proof
  apply StatMech.Sharpness.sct_c_to_one G M c hLpos hM hsqueeze hle_one

/--
[sct_cInf_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean)
-/
@[path]
private lemma sct_cInf_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : ℕ → ℝ}
  {sites : ℕ → Finset ℕ}
  {m : ℕ → ℕ → ℝ}
  {o : ℕ → ℕ}
  {n : ℕ}
-- given
  (hne : ∀ n, (sites n).Nonempty)
  (ho : ∀ n, o n ∈ sites n)
  (hoM : ∀ n, m n (o n) = M n)
  (hMne : ∀ n, M n ≠ 0) :
-- imply
  sct_cInf M sites m hne n ≤ 1 := by
-- proof
  apply StatMech.Sharpness.sct_cInf_le_one G M sites m hne o ho hoM hMne n

/--
[sct_ratio_le_cInf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean)
-/
@[path]
private lemma sct_ratio_le_cInf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : ℕ → ℝ}
  {sites : ℕ → Finset ℕ}
  {m : ℕ → ℕ → ℝ}
  {n : ℕ}
-- given
  (hne : ∀ n, (sites n).Nonempty)
  (hmpos : ∀ n y, y ∈ sites n → 0 < m n y)
  (hMnn : ∀ n, 0 ≤ M n)
  (hbox : ∀ n y, y ∈ sites n → m n y ≤ M (2 * n)) :
-- imply
  M n / M (2 * n) ≤ sct_cInf M sites m hne n := by
-- proof
  apply StatMech.Sharpness.sct_ratio_le_cInf G M sites m hne hmpos hMnn hbox n

/--
[sct_cInf_to_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean)
-/
@[path]
private lemma sct_cInf_to_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M : ℕ → ℝ}
  {sites : ℕ → Finset ℕ}
  {m : ℕ → ℕ → ℝ}
  {L : ℝ}
  {o : ℕ → ℕ}
-- given
  (hne : ∀ n, (sites n).Nonempty)
  (hLpos : 0 < L)
  (hM : Tendsto M atTop (𝓝 L))
  (hmpos : ∀ n y, y ∈ sites n → 0 < m n y)
  (hMnn : ∀ n, 0 ≤ M n)
  (hMne : ∀ n, M n ≠ 0)
  (ho : ∀ n, o n ∈ sites n)
  (hoM : ∀ n, m n (o n) = M n)
  (hbox : ∀ n y, y ∈ sites n → m n y ≤ M (2 * n)) :
-- imply
  Tendsto (sct_cInf M sites m hne) atTop (𝓝 1) := by
-- proof
  apply StatMech.Sharpness.sct_cInf_to_one G M sites m hne hLpos hM hmpos hMnn hMne o ho hoM hbox

/--
[sct_cInfDep_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean)
-/
@[path]
private lemma sct_cInfDep_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ι : ℕ → Type*}
  [∀ n, DecidableEq (ι n)]
  {M : ℕ → ℝ}
  {sites : (n : ℕ) → Finset (ι n)}
  {m : (n : ℕ) → ι n → ℝ}
  {o : (n : ℕ) → ι n}
  {n : ℕ}
-- given
  (hne : ∀ n, (sites n).Nonempty)
  (ho : ∀ n, o n ∈ sites n)
  (hoM : ∀ n, m n (o n) = M n)
  (hMne : ∀ n, M n ≠ 0) :
-- imply
  sct_cInfDep ι M sites m hne n ≤ 1 := by
-- proof
  apply StatMech.Sharpness.sct_cInfDep_le_one G ι M sites m hne o ho hoM hMne n

/--
[sct_ratio_le_cInfDep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean)
-/
@[path]
private lemma sct_ratio_le_cInfDep_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ι : ℕ → Type*}
  [∀ n, DecidableEq (ι n)]
  {M : ℕ → ℝ}
  {sites : (n : ℕ) → Finset (ι n)}
  {m : (n : ℕ) → ι n → ℝ}
  {n : ℕ}
-- given
  (hne : ∀ n, (sites n).Nonempty)
  (hmpos : ∀ n y, y ∈ sites n → 0 < m n y)
  (hMnn : ∀ n, 0 ≤ M n)
  (hbox : ∀ n y, y ∈ sites n → m n y ≤ M (2 * n)) :
-- imply
  M n / M (2 * n) ≤ sct_cInfDep ι M sites m hne n := by
-- proof
  apply StatMech.Sharpness.sct_ratio_le_cInfDep G ι M sites m hne hmpos hMnn hbox n

/--
[sct_cInfDep_to_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean)
-/
@[path]
private lemma sct_cInfDep_to_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ι : ℕ → Type*}
  [∀ n, DecidableEq (ι n)]
  {M : ℕ → ℝ}
  {sites : (n : ℕ) → Finset (ι n)}
  {m : (n : ℕ) → ι n → ℝ}
  {L : ℝ}
  {o : (n : ℕ) → ι n}
-- given
  (hne : ∀ n, (sites n).Nonempty)
  (hLpos : 0 < L)
  (hM : Tendsto M atTop (𝓝 L))
  (hmpos : ∀ n y, y ∈ sites n → 0 < m n y)
  (hMnn : ∀ n, 0 ≤ M n)
  (hMne : ∀ n, M n ≠ 0)
  (ho : ∀ n, o n ∈ sites n)
  (hoM : ∀ n, m n (o n) = M n)
  (hbox : ∀ n y, y ∈ sites n → m n y ≤ M (2 * n)) :
-- imply
  Tendsto (sct_cInfDep ι M sites m hne) atTop (𝓝 1) := by
-- proof
  apply StatMech.Sharpness.sct_cInfDep_to_one G ι M sites m hne hLpos hM hmpos hMnn hMne o ho hoM hbox

/--
[sct_cInfDep_to_one_of_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOne.lean)
-/
@[path]
private lemma sct_cInfDep_to_one_of_monotone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ι : ℕ → Type*}
  [∀ n, DecidableEq (ι n)]
  {M : ℕ → ℝ}
  {sites : (n : ℕ) → Finset (ι n)}
  {m : (n : ℕ) → ι n → ℝ}
  {o : (n : ℕ) → ι n}
-- given
  (hne : ∀ n, (sites n).Nonempty)
  (hmono : Monotone M)
  (hub : ∀ n, M n ≤ 1)
  (hM0 : 0 < M 0)
  (hmpos : ∀ n y, y ∈ sites n → 0 < m n y)
  (ho : ∀ n, o n ∈ sites n)
  (hoM : ∀ n, m n (o n) = M n)
  (hbox : ∀ n y, y ∈ sites n → m n y ≤ M (2 * n)) :
-- imply
  Tendsto (sct_cInfDep ι M sites m hne) atTop (𝓝 1) := by
-- proof
  apply StatMech.Sharpness.sct_cInfDep_to_one_of_monotone G ι M sites m hne hmono hub hM0 hmpos o ho hoM hbox


-- created on 2026-10-23
