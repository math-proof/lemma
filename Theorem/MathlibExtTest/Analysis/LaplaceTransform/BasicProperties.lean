/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/LaplaceTransform/BasicProperties.lean -/


import Lemma.Real.LaplaceTransform.BasicProperties
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-!
# Checks for the elementary Laplace-transform API

Anonymous examples exercising every endpoint of `BasicProperties`.
-/


example (s : ℂ) : HasLaplace (fun _ : ℝ => (0 : E)) s 0 :=
  hasLaplace_zero s

example (f g : ℝ → E) (s : ℂ) (hf : LaplaceConvergent f s)
    (hg : LaplaceConvergent g s) :
    HasLaplace (f + g) s (laplace f s + laplace g s) :=
  hasLaplace_add hf hg

example (f g : ℝ → E) (s : ℂ) (hf : LaplaceConvergent f s)
    (hg : LaplaceConvergent g s) :
    HasLaplace (f - g) s (laplace f s - laplace g s) :=
  hasLaplace_sub hf hg

example (f : ℝ → E) (s : ℂ) (hf : LaplaceConvergent f s) (c : ℂ) :
    LaplaceConvergent (fun t => c • f t) s :=
  hf.const_smul c

example (f : ℝ → E) (s : ℂ) (hf : LaplaceConvergent f s) (c : ℂ) :
    HasLaplace (fun t => c • f t) s (c • laplace f s) :=
  hasLaplace_const_smul hf c

example (f : ℝ → E) (s : ℂ) (hf : LaplaceConvergent f s) :
    LaplaceConvergent f (s + 1) :=
  hf.mono_re (by simp only [Complex.add_re, Complex.one_re]; linarith)

example (f : ℝ → E) (s a : ℂ) :
    LaplaceConvergent (fun t => Complex.exp (a * (t : ℂ)) • f t) s ↔
      LaplaceConvergent f (s - a) :=
  LaplaceConvergent.exp_smul s a

example (f : ℝ → E) (s a : ℂ) :
    laplace (fun t => Complex.exp (a * (t : ℂ)) • f t) s =
      laplace f (s - a) :=
  laplace_exp_smul f s a

example (f : ℝ → E) (s a : ℂ) (v : E) :
    HasLaplace (fun t => Complex.exp (a * (t : ℂ)) • f t) s v ↔
      HasLaplace f (s - a) v :=
  hasLaplace_exp_smul_iff s a v

example : HasLaplace (fun _ : ℝ => (1 : ℂ)) 1 1 := by
  simpa using hasLaplace_one (s := (1 : ℂ)) (by simp)

