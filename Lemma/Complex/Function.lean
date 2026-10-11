import Mathlib
import sympy.Basic
import sympy.functions.special.elliptic.Function


/--
[Function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean)
-/
@[path]
private lemma is_lattice_periodic_const_is
-- given
  (L : PeriodPair)
  (c : ℂ) :
-- imply
  L.IsLatticePeriodic fun _ ↦ c := by
-- proof
  apply PeriodPair.isLatticePeriodic_const L c

/--
[Function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean)
-/
@[path]
private lemma is_elliptic_function_const_is
-- given
  (L : PeriodPair)
  (c : ℂ) :
-- imply
  L.IsEllipticFunction fun _ ↦ c := by
-- proof
  apply PeriodPair.IsEllipticFunction.const L c

/--
[Function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean)
-/
@[path]
private lemma is_elliptic_function_add_is
-- given
  (L : PeriodPair)
  (f g : ℂ → ℂ)
  (hf : L.IsEllipticFunction f)
  (hg : L.IsEllipticFunction g) :
-- imply
  L.IsEllipticFunction (f + g) := by
-- proof
  apply PeriodPair.IsEllipticFunction.add hf hg

/--
[Function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean)
-/
@[path]
private lemma is_elliptic_function_mul_is
-- given
  (L : PeriodPair)
  (f g : ℂ → ℂ)
  (hf : L.IsEllipticFunction f)
  (hg : L.IsEllipticFunction g) :
-- imply
  L.IsEllipticFunction (f * g) := by
-- proof
  apply PeriodPair.IsEllipticFunction.mul hf hg


-- created on 2026-10-11
