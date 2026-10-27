import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryMonomial
open Finset StatMech StatMech.Ising


/--
[IsSpinMonomial.xnor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryMonomial.lean)
-/
@[path]
private lemma xnor_eq
  [Fintype V]
  [DecidableEq V]
  {f : ConfigSpace V -> Real}
  {a q : ConfigSpace V}
-- given
  (hf : IsSpinMonomial f) :
-- imply
  f (xnor a q) = f a * f q := by
-- proof
  apply StatMech.Ising.IsSpinMonomial.xnor hf a q

/--
[IsSpinMonomial.eq_pm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryMonomial.lean)
-/
@[path]
private lemma eq_pm_eq
  [Fintype V]
  [DecidableEq V]
  {f : ConfigSpace V -> Real}
  {s : ConfigSpace V}
-- given
  (hf : IsSpinMonomial f) :
-- imply
  f s = 1 ∨ f s = -1 := by
-- proof
  apply StatMech.Ising.IsSpinMonomial.eq_pm hf s

/--
[IsSpinMonomial.one_add_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryMonomial.lean)
-/
@[path]
private lemma one_add_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {f : ConfigSpace V -> Real}
  {s : ConfigSpace V}
-- given
  (hf : IsSpinMonomial f) :
-- imply
  0 <= 1 + f s := by
-- proof
  apply StatMech.Ising.IsSpinMonomial.one_add_nonneg hf s

/--
[IsSpinMonomial.one_sub_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryMonomial.lean)
-/
@[path]
private lemma one_sub_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {f : ConfigSpace V -> Real}
  {s : ConfigSpace V}
-- given
  (hf : IsSpinMonomial f) :
-- imply
  0 <= 1 - f s := by
-- proof
  apply StatMech.Ising.IsSpinMonomial.one_sub_nonneg hf s

/--
[ginibre_cross_monomial_inner_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryMonomial.lean)
-/
@[path]
private lemma ginibre_cross_monomial_inner_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {q : ConfigSpace V}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hdom : forall v, |h v| <= hPlus v)
  (f g : ConfigSpace V -> Real)
  (hf : IsSpinMonomial f)
  (hg : IsSpinMonomial g) :
-- imply
  0 <= ∑ a : ConfigSpace V, wJ E J hPlus a * wJ E J h (xnor a q) * ((f a + f (xnor a q)) * (g a - g (xnor a q))) := by
-- proof
  apply StatMech.Ising.ginibre_cross_monomial_inner_nonneg E J hPlus h hJ hdom f g hf hg q

/--
[ginibre_cross_monomial_numerator_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryMonomial.lean)
-/
@[path]
private lemma ginibre_cross_monomial_numerator_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hdom : forall v, |h v| <= hPlus v)
  (f g : ConfigSpace V -> Real)
  (hf : IsSpinMonomial f)
  (hg : IsSpinMonomial g) :
-- imply
  0 <= ∑ a : ConfigSpace V, ∑ b : ConfigSpace V, wJ E J hPlus a * wJ E J h b * ((f a + f b) * (g a - g b)) := by
-- proof
  apply StatMech.Ising.ginibre_cross_monomial_numerator_nonneg E J hPlus h hJ hdom f g hf hg

/--
[ginibre_boundary_monomial_correlation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryMonomial.lean)
-/
@[path]
private lemma ginibre_boundary_monomial_correlation_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hdom : forall v, |h v| <= hPlus v)
  (f g : ConfigSpace V -> Real)
  (hf : IsSpinMonomial f)
  (hg : IsSpinMonomial g) :
-- imply
  expJ E J hPlus (fun s => f s * g s) - expJ E J h (fun s => f s * g s) >= expJ E J hPlus f * expJ E J h g - expJ E J hPlus g * expJ E J h f := by
-- proof
  apply StatMech.Ising.ginibre_boundary_monomial_correlation E J hPlus h hJ hdom f g hf hg

/--
[ginibre_boundary_monomial_product_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryMonomial.lean)
-/
@[path]
private lemma ginibre_boundary_monomial_product_mono_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hdom : forall v, |h v| <= hPlus v)
  (f g : ConfigSpace V -> Real)
  (hf : IsSpinMonomial f)
  (hg : IsSpinMonomial g) :
-- imply
  expJ E J h (fun s => f s * g s) <= expJ E J hPlus (fun s => f s * g s) := by
-- proof
  apply StatMech.Ising.ginibre_boundary_monomial_product_mono E J hPlus h hJ hdom f g hf hg


-- created on 2026-10-23
