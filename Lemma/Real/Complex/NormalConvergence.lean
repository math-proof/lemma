import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.NormalConvergence
open Set Metric Filter Topology ENNReal


/--
[ConvergesNormallyOn.summable_toReal_supNormOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
private lemma ConvergesNormallyOn_summable_toReal_supNormOn_eq
  [SeminormedAddCommGroup E]
  {f : ℕ → X → E}
  {S : Set X}
-- given
  (hf : ConvergesNormallyOn f S) :
-- imply
  Summable (fun n => (supNormOn (f n) S).toReal) := by
-- proof
  apply ConvergesNormallyOn.summable_toReal_supNormOn hf

/--
[ConvergesNormallyOn.summable_norm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
private lemma ConvergesNormallyOn_summable_norm_eq
  [SeminormedAddCommGroup E]
  {f : Nat → X → E}
  {S : Set X}
  {x : X}
-- given
  (hf : ConvergesNormallyOn f S)
  (hx : x ∈ S) :
-- imply
  Summable (fun n => norm (f n x)) := by
-- proof
  apply ConvergesNormallyOn.summable_norm hf hx

/--
[ConvergesLocallyNormallyOn.summable_norm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
private lemma ConvergesLocallyNormallyOn_summable_norm_eq
  [TopologicalSpace X] [SeminormedAddCommGroup E]
  {f : Nat → X → E}
  {S : Set X}
  {x : X}
-- given
  (hf : ConvergesLocallyNormallyOn f S)
  (hx : x ∈ S) :
-- imply
  Summable (fun n => norm (f n x)) := by
-- proof
  apply ConvergesLocallyNormallyOn.summable_norm hf hx

/--
[ConvergesNormallyOn.tendstoUniformlyOn_tsum_nat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
private lemma ConvergesNormallyOn_tendstoUniformlyOn_tsum_nat_eq
  [NormedAddCommGroup E] [CompleteSpace E]
  {f : ℕ → X → E}
  {S : Set X}
-- given
  (hf : ConvergesNormallyOn f S) :
-- imply
  TendstoUniformlyOn (fun N z => ∑ n ∈ Finset.range N, f n z)
    (fun z => ∑' n, f n z) atTop S := by
-- proof
  apply ConvergesNormallyOn.tendstoUniformlyOn_tsum_nat hf

/--
[ConvergesLocallyNormallyOn.deriv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
private lemma ConvergesLocallyNormallyOn_deriv_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℕ → ℂ → E}
  {S : Set ℂ}
-- given
  (hf : ConvergesLocallyNormallyOn f S)
  (hS : IsOpen S)
  (holo : ∀ n, DifferentiableOn ℂ (f n) S) :
-- imply
  ConvergesLocallyNormallyOn (fun n z => _root_.deriv (f n) z) S := by
-- proof
  apply ConvergesLocallyNormallyOn.deriv hf hS holo

/--
[ConvergesLocallyNormallyOn.tendstoLocallyUniformlyOn_tsum_nat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
private lemma ConvergesLocallyNormallyOn_tendstoLocallyUniformlyOn_tsum_nat_eq
  [TopologicalSpace X] [NormedAddCommGroup E] [CompleteSpace E]
  {f : Nat → X → E}
  {S : Set X}
-- given
  (hf : ConvergesLocallyNormallyOn f S) :
-- imply
  TendstoLocallyUniformlyOn
    (fun N x => Finset.sum (Finset.range N) fun n => f n x)
    (fun x => ∑' n, f n x) atTop S := by
-- proof
  apply ConvergesLocallyNormallyOn.tendstoLocallyUniformlyOn_tsum_nat hf

/--
[ConvergesLocallyNormallyOn.hasDerivAt_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
private lemma ConvergesLocallyNormallyOn_hasDerivAt_tsum_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : Nat → Complex → E}
  {S : Set Complex}
  {z : Complex}
-- given
  (hf : ConvergesLocallyNormallyOn f S)
  (hS : IsOpen S)
  (holo : ∀ n, DifferentiableOn Complex (f n) S)
  (hz : z ∈ S) :
-- imply
  HasDerivAt (fun w => ∑' n, f n w) (∑' n, _root_.deriv (f n) z) z := by
-- proof
  apply ConvergesLocallyNormallyOn.hasDerivAt_tsum hf hS holo hz


-- created on 2026-10-20
