import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.LaplaceTransform.BasicProperties
open MeasureTheory


/--
[LaplaceConvergent.const_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
private lemma LaplaceConvergent_const_smul_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E}
  {s c : ℂ}
-- given
  (hf : LaplaceConvergent f s) :
-- imply
  LaplaceConvergent (fun t => c • f t) s := by
-- proof
  apply LaplaceConvergent.const_smul hf c

/--
[hasLaplace_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
private lemma hasLaplace_zero_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {s : ℂ} :
-- imply
  HasLaplace (fun _ : ℝ => (0 : E)) s 0 := by
-- proof
  apply hasLaplace_zero s

/--
[hasLaplace_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
private lemma hasLaplace_add_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : ℝ → E}
  {s : ℂ}
-- given
  (hf : LaplaceConvergent f s)
  (hg : LaplaceConvergent g s) :
-- imply
  HasLaplace (f + g) s (laplace f s + laplace g s) := by
-- proof
  apply hasLaplace_add hf hg

/--
[hasLaplace_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
private lemma hasLaplace_sub_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : ℝ → E}
  {s : ℂ}
-- given
  (hf : LaplaceConvergent f s)
  (hg : LaplaceConvergent g s) :
-- imply
  HasLaplace (f - g) s (laplace f s - laplace g s) := by
-- proof
  apply hasLaplace_sub hf hg

/--
[hasLaplace_const_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
private lemma hasLaplace_const_smul_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E}
  {s c : ℂ}
-- given
  (hf : LaplaceConvergent f s) :
-- imply
  HasLaplace (fun t => c • f t) s (c • laplace f s) := by
-- proof
  apply hasLaplace_const_smul hf c

/--
[LaplaceConvergent.mono_re](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
private lemma LaplaceConvergent_mono_re_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E}
  {s w : ℂ}
-- given
  (hf : LaplaceConvergent f s)
  (hsw : s.re ≤ w.re) :
-- imply
  LaplaceConvergent f w := by
-- proof
  apply LaplaceConvergent.mono_re hf hsw

/--
[LaplaceConvergent.exp_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
private lemma LaplaceConvergent_exp_smul_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E}
  {s a : ℂ} :
-- imply
  LaplaceConvergent (fun t => Complex.exp (a * (t : ℂ)) • f t) s ↔
    LaplaceConvergent f (s - a) := by
-- proof
  apply LaplaceConvergent.exp_smul s a

/--
[laplace_exp_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
private lemma laplace_exp_smul_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E}
  {s a : ℂ} :
-- imply
  laplace (fun t => Complex.exp (a * (t : ℂ)) • f t) s =
    laplace f (s - a) := by
-- proof
  apply laplace_exp_smul f s a

/--
[hasLaplace_exp_smul_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
private lemma hasLaplace_exp_smul_iff_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℝ → E}
  {s a : ℂ}
  {v : E} :
-- imply
  HasLaplace (fun t => Complex.exp (a * (t : ℂ)) • f t) s v ↔
    HasLaplace f (s - a) v := by
-- proof
  apply hasLaplace_exp_smul_iff s a v

/--
[hasLaplace_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/BasicProperties.lean)
-/
@[path]
private lemma hasLaplace_one_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {s : ℂ}
-- given
  (hs : 0 < s.re) :
-- imply
  HasLaplace (fun _ : ℝ => (1 : ℂ)) s s⁻¹ := by
-- proof
  apply hasLaplace_one hs


-- created on 2026-10-20
