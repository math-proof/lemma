import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.Elliptic.Function
open PeriodPair


/--
[Function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean)
-/
@[path]
private lemma isLatticePeriodic_const_eq
-- given
  (L : PeriodPair)
  (c : ℂ) :
-- imply
  L.IsLatticePeriodic fun _ ↦ c :=
-- proof
  isLatticePeriodic_const L c


/--
[Function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean)
-/
@[path]
private lemma isEllipticFunction_const_eq
-- given
  (L : PeriodPair)
  (c : ℂ) :
-- imply
  L.IsEllipticFunction fun _ ↦ c :=
-- proof
  IsEllipticFunction.const L c


/--
[Function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean)
-/
@[path]
private lemma isEllipticFunction_add_eq
-- given
  (L : PeriodPair)
  (f g : ℂ → ℂ)
  (hf : L.IsEllipticFunction f)
  (hg : L.IsEllipticFunction g) :
-- imply
  L.IsEllipticFunction (f + g) :=
-- proof
  IsEllipticFunction.add hf hg


/--
[Function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean)
-/
@[path]
private lemma isEllipticFunction_mul_eq
-- given
  (L : PeriodPair)
  (f g : ℂ → ℂ)
  (hf : L.IsEllipticFunction f)
  (hg : L.IsEllipticFunction g) :
-- imply
  L.IsEllipticFunction (f * g) :=
-- proof
  IsEllipticFunction.mul hf hg



-- created on 2026-10-11
-- updated on 2026-11-22
