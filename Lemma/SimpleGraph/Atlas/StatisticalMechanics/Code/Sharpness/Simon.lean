import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.Simon
open Finset StatMech StatMech.Sharpness


/--
[wJ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma wJ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {s : ConfigSpace V}
-- given
  (hf : V → ℝ) :
-- imply
  0 < wJ E J hf s := by
-- proof
  apply StatMech.Sharpness.wJ_pos E J hf s

/--
[wJ_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma wJ_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {s : ConfigSpace V}
-- given
  (hf : V → ℝ) :
-- imply
  0 ≤ wJ E J hf s := by
-- proof
  apply StatMech.Sharpness.wJ_nonneg E J hf s

/--
[ZJ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma ZJ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
-- given
  (hf : V → ℝ) :
-- imply
  0 < ZJ E J hf := by
-- proof
  apply StatMech.Sharpness.ZJ_pos E J hf

/--
[inner_sum_nonneg'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma inner_sum_nonneg'_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {ce de : Sym2 V → ℝ}
  {cx dx : V → ℝ}
  {obs : ConfigSpace V → ℝ}
-- given
  (hce : ∀ e ∈ E, 0 ≤ ce e)
  (hde : ∀ e ∈ E, 0 ≤ de e)
  (hcx : ∀ x, 0 ≤ cx x)
  (hdx : ∀ x, 0 ≤ dx x)
  (hobs : IsSpinMonomial obs) :
-- imply
  0 ≤ ∑ s : ConfigSpace V, obs s * ((∏ e ∈ E, (ce e + bond s e * de e)) * (∏ x : V, (cx x + spin s x * dx x))) := by
-- proof
  apply StatMech.Sharpness.inner_sum_nonneg' E ce de cx dx hce hde hcx hdx obs hobs

/--
[doubled_wJ_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma doubled_wJ_factor_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {σ q : ConfigSpace V}
-- given
  (hf : V → ℝ) :
-- imply
  wJ E J hf σ * wJ E J hf (xnor σ q) = (∏ e ∈ E, (Real.cosh (J e * (1 + bond q e)) + bond σ e * Real.sinh (J e * (1 + bond q e)))) * (∏ x : V, (Real.cosh (hf x * (1 + spin q x)) + spin σ x * Real.sinh (hf x * (1 + spin q x)))) := by
-- proof
  apply StatMech.Sharpness.doubled_wJ_factor E J hf σ q

/--
[inner_q_nonneg_J](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma inner_q_nonneg_J_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  {q : ConfigSpace V}
-- given
  (hf : V → ℝ)
  (hJ : ∀ e ∈ E, 0 ≤ J e)
  (hhf : ∀ x, 0 ≤ hf x) :
-- imply
  0 ≤ ∑ σ : ConfigSpace V, (spinProd (A ∆ B) σ * wJ E J hf σ * wJ E J hf (xnor σ q) - spinProd A σ * wJ E J hf σ * (spinProd B (xnor σ q) * wJ E J hf (xnor σ q))) := by
-- proof
  apply StatMech.Sharpness.inner_q_nonneg_J E J hf hJ hhf A B q

/--
[unnorm_gks2_J](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma unnorm_gks2_J_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
-- given
  (hf : V → ℝ)
  (hJ : ∀ e ∈ E, 0 ≤ J e)
  (hhf : ∀ x, 0 ≤ hf x) :
-- imply
  (∑ s, spinProd A s * wJ E J hf s) * (∑ s, spinProd B s * wJ E J hf s) ≤ (∑ s, spinProd (A ∆ B) s * wJ E J hf s) * (∑ s, wJ E J hf s) := by
-- proof
  apply StatMech.Sharpness.unnorm_gks2_J E J hf hJ hhf A B

/--
[gks_second_J](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma gks_second_J_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
-- given
  (hf : V → ℝ)
  (hJ : ∀ e ∈ E, 0 ≤ J e)
  (hhf : ∀ x, 0 ≤ hf x) :
-- imply
  expJ E J hf (spinProd A) * expJ E J hf (spinProd B) ≤ expJ E J hf (spinProd (A ∆ B)) := by
-- proof
  apply StatMech.Sharpness.gks_second_J E J hf hJ hhf A B

/--
[wJ_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma wJ_insert_eq
  [Fintype V]
  [DecidableEq V]
  {e₀ : Sym2 V}
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {s : ConfigSpace V}
-- given
  (he : e₀ ∉ E)
  (hf : V → ℝ) :
-- imply
  wJ (insert e₀ E) J hf s = Real.exp (J e₀ * bond s e₀) * wJ E J hf s := by
-- proof
  apply StatMech.Sharpness.wJ_insert e₀ E he J hf s

/--
[bond_eq_spinProd_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma bond_eq_spinProd_pair_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {x y : V}
-- given
  (hxy : x ≠ y) :
-- imply
  bond s s(x, y) = spinProd {x, y} s := by
-- proof
  apply StatMech.Sharpness.bond_eq_spinProd_pair s hxy

/--
[griffiths_mono_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma griffiths_mono_insert_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {x y : V}
  {A : Finset V}
-- given
  (hf : V → ℝ)
  (hJ : ∀ e ∈ E, 0 ≤ J e)
  (hhf : ∀ x, 0 ≤ hf x)
  (hxy : x ≠ y)
  (he : s(x, y) ∉ E)
  (hJe : 0 ≤ J s(x, y)) :
-- imply
  expJ E J hf (spinProd A) ≤ expJ (insert s(x, y) E) J hf (spinProd A) := by
-- proof
  apply StatMech.Sharpness.griffiths_mono_insert E J hf hJ hhf hxy he hJe A

/--
[exists_pair_of_not_isDiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma exists_pair_of_not_isDiag_eq
  [Fintype V]
  [DecidableEq V]
  {e₀ : Sym2 V}
-- given
  (h : ¬ e₀.IsDiag) :
-- imply
  ∃ x y : V, x ≠ y ∧ e₀ = s(x, y) := by
-- proof
  apply StatMech.Sharpness.exists_pair_of_not_isDiag h

/--
[griffiths_mono_insert_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma griffiths_mono_insert_edge_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {e₀ : Sym2 V}
  {A : Finset V}
-- given
  (hf : V → ℝ)
  (hJ : ∀ e ∈ E, 0 ≤ J e)
  (hhf : ∀ x, 0 ≤ hf x)
  (hdiag : ¬ e₀.IsDiag)
  (he : e₀ ∉ E)
  (hJe : 0 ≤ J e₀) :
-- imply
  expJ E J hf (spinProd A) ≤ expJ (insert e₀ E) J hf (spinProd A) := by
-- proof
  apply StatMech.Sharpness.griffiths_mono_insert_edge E J hf hJ hhf hdiag he hJe A

/--
[griffiths_mono_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma griffiths_mono_union_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hf : V → ℝ)
  (hhf : ∀ x, 0 ≤ hf x) :
-- imply
  ∀ D : Finset (Sym2 V), Disjoint D E → (∀ e ∈ D, ¬ e.IsDiag) → (∀ e ∈ D ∪ E, 0 ≤ J e) → expJ E J hf (spinProd A) ≤ expJ (D ∪ E) J hf (spinProd A) := by
-- proof
  apply StatMech.Sharpness.griffiths_mono_union E J hf hhf A

/--
[griffiths_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma griffiths_mono_eq
  [Fintype V]
  [DecidableEq V]
  {E₁ E₂ : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {A : Finset V}
-- given
  (hf : V → ℝ)
  (hsub : E₁ ⊆ E₂)
  (hJ : ∀ e ∈ E₂, 0 ≤ J e)
  (hhf : ∀ x, 0 ≤ hf x)
  (hdiag : ∀ e ∈ E₂, e ∉ E₁ → ¬ e.IsDiag) :
-- imply
  expJ E₁ J hf (spinProd A) ≤ expJ E₂ J hf (spinProd A) := by
-- proof
  apply StatMech.Sharpness.griffiths_mono E₁ E₂ J hf hsub hJ hhf hdiag A

/--
[griffiths_mono_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma griffiths_mono_spin_eq
  [Fintype V]
  [DecidableEq V]
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
  apply StatMech.Sharpness.griffiths_mono_spin E₁ E₂ J hf hsub hJ hhf hdiag z

/--
[griffiths_mono_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean)
-/
@[path]
private lemma griffiths_mono_pair_eq
  [Fintype V]
  [DecidableEq V]
  {E₁ E₂ : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {x y : V}
-- given
  (hf : V → ℝ)
  (hsub : E₁ ⊆ E₂)
  (hJ : ∀ e ∈ E₂, 0 ≤ J e)
  (hhf : ∀ x, 0 ≤ hf x)
  (hdiag : ∀ e ∈ E₂, e ∉ E₁ → ¬ e.IsDiag) :
-- imply
  expJ E₁ J hf (spinProd {x, y}) ≤ expJ E₂ J hf (spinProd {x, y}) := by
-- proof
  apply StatMech.Sharpness.griffiths_mono_pair E₁ E₂ J hf hsub hJ hhf hdiag x y


-- created on 2026-10-23
