import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.CovLowerBound
open Finset StatMech StatMech.OSSS StatMech.OSSS.CovLowerBound


/--
[coordI_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CovLowerBound.lean)
-/
@[path]
private lemma coordI_setOpen_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  coordI e (setOpen e ω) = 1 := by
-- proof
  apply StatMech.OSSS.CovLowerBound.coordI_setOpen e ω

/--
[coordI_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CovLowerBound.lean)
-/
@[path]
private lemma coordI_setClosed_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  coordI e (setClosed e ω) = 0 := by
-- proof
  apply StatMech.OSSS.CovLowerBound.coordI_setClosed e ω

/--
[coordI_eq_tree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CovLowerBound.lean)
-/
@[path]
private lemma coordI_eq_tree_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E} :
-- imply
  coordI e = (DecisionTree.node e (DecisionTree.leaf true) (DecisionTree.leaf false)).evalR := by
-- proof
  apply StatMech.OSSS.CovLowerBound.coordI_eq_tree e

/--
[cov_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CovLowerBound.lean)
-/
@[path]
private lemma cov_const_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {c : ℝ}
  {G : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  cov ν (fun _ => c) G = 0 := by
-- proof
  apply StatMech.OSSS.CovLowerBound.cov_const hν c G

/--
[cov_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CovLowerBound.lean)
-/
@[path]
private lemma cov_leaf_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {b : Bool}
  {G : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  cov ν (DecisionTree.leaf b).evalR G = 0 := by
-- proof
  apply StatMech.OSSS.CovLowerBound.cov_leaf hν b G

/--
[cov_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CovLowerBound.lean)
-/
@[path]
private lemma cov_comm_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {ν : E → Bool → ℝ}
  {F G : ConfigSpace E → ℝ} :
-- imply
  cov ν F G = cov ν G F := by
-- proof
  apply StatMech.OSSS.CovLowerBound.cov_comm ν F G

/--
[cov_coordI_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CovLowerBound.lean)
-/
@[path]
private lemma cov_coordI_indep_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {H : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν)
  (hH : ∀ ω, H (flipAt e ω) = H ω) :
-- imply
  cov ν (coordI e) H = 0 := by
-- proof
  apply StatMech.OSSS.CovLowerBound.cov_coordI_indep hν e H hH

/--
[cov_coordI](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CovLowerBound.lean)
-/
@[path]
private lemma cov_coordI_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  cov ν (coordI e) g = ν e true * ν e false * expect ν (fun ω => g (setOpen e ω) - g (setClosed e ω)) := by
-- proof
  apply StatMech.OSSS.CovLowerBound.cov_coordI hν e g

/--
[infl_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CovLowerBound.lean)
-/
@[path]
private lemma infl_mono_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {g : ConfigSpace E → ℝ}
  {ν : E → Bool → ℝ}
  {e : E}
-- given
  (hg : Monotone g) :
-- imply
  infl ν g e = expect ν (fun ω => g (setOpen e ω) - g (setClosed e ω)) := by
-- proof
  apply StatMech.OSSS.CovLowerBound.infl_mono hg ν e

/--
[cov_coordI_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CovLowerBound.lean)
-/
@[path]
private lemma cov_coordI_mono_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {g : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hν : IsProbWeight ν)
  (hg : Monotone g) :
-- imply
  cov ν (coordI e) g = ν e true * ν e false * infl ν g e := by
-- proof
  apply StatMech.OSSS.CovLowerBound.cov_coordI_mono hν hg e

/--
[siteVar_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CovLowerBound.lean)
-/
@[path]
private lemma siteVar_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  0 ≤ ν e true * ν e false := by
-- proof
  apply StatMech.OSSS.CovLowerBound.siteVar_nonneg hν e

/--
[cov_coordI_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CovLowerBound.lean)
-/
@[path]
private lemma cov_coordI_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {g : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hν : IsProbWeight ν)
  (hg : Monotone g) :
-- imply
  0 ≤ cov ν (coordI e) g := by
-- proof
  apply StatMech.OSSS.CovLowerBound.cov_coordI_nonneg hν hg e

/--
[cov_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CovLowerBound.lean)
-/
@[path]
private lemma cov_lower_bound_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  [Fintype κ]
  [Nonempty κ]
  {A : Set (ConfigSpace E)}
  {f : ConfigSpace E → ℝ}
  {T : κ → DecisionTree E}
  {R : κ → E → ℝ}
  {c₀ : ℝ}
  {D : ℝ}
-- given
  (hν : IsProbWeight ν)
  (hA : IsIncreasing A)
  (hf : f = A.indicator (fun _ => (1 : ℝ)))
  (hT : ∀ k, (T k).evalR = f)
  (hR : ∀ k e, reveal ν (T k) e ≤ R k e)
  (hc₀nn : 0 ≤ c₀)
  (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
  (hDnn : 0 ≤ D)
  (hD : ∀ e, (∑ k, R k e) ≤ D) :
-- imply
  (Fintype.card κ : ℝ) * c₀ * var ν f ≤ D * ∑ e, cov ν (coordI e) f := by
-- proof
  apply StatMech.OSSS.CovLowerBound.cov_lower_bound hν hA hf T hT R hR c₀ hc₀nn hc₀ D hDnn hD

/--
[cov_lower_bound_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CovLowerBound.lean)
-/
@[path]
private lemma cov_lower_bound_div_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  [Fintype κ]
  [Nonempty κ]
  {A : Set (ConfigSpace E)}
  {f : ConfigSpace E → ℝ}
  {T : κ → DecisionTree E}
  {R : κ → E → ℝ}
  {c₀ : ℝ}
  {D : ℝ}
-- given
  (hν : IsProbWeight ν)
  (hA : IsIncreasing A)
  (hf : f = A.indicator (fun _ => (1 : ℝ)))
  (hT : ∀ k, (T k).evalR = f)
  (hR : ∀ k e, reveal ν (T k) e ≤ R k e)
  (hc₀nn : 0 ≤ c₀)
  (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
  (hDpos : 0 < D)
  (hD : ∀ e, (∑ k, R k e) ≤ D) :
-- imply
  ((Fintype.card κ : ℝ) * c₀ / D) * var ν f ≤ ∑ e, cov ν (coordI e) f := by
-- proof
  apply StatMech.OSSS.CovLowerBound.cov_lower_bound_div hν hA hf T hT R hR c₀ hc₀nn hc₀ D hDpos hD

/--
[cov_lower_bound_poincare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/CovLowerBound.lean)
-/
@[path]
private lemma cov_lower_bound_poincare_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {A : Set (ConfigSpace E)}
  {φ : ConfigSpace E → Bool}
  {c₀ : ℝ}
-- given
  (hν : IsProbWeight ν)
  (hA : IsIncreasing A)
  (hφ : (fullTreeUniv φ).evalR = A.indicator (fun _ => (1 : ℝ)))
  (hc₀nn : 0 ≤ c₀)
  (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false) :
-- imply
  c₀ * var ν (A.indicator (fun _ => (1 : ℝ))) ≤ ∑ e, cov ν (coordI e) (A.indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.OSSS.CovLowerBound.cov_lower_bound_poincare hν hA φ hφ c₀ hc₀nn hc₀


-- created on 2026-10-23
