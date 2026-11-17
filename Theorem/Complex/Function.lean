module

public import Mathlib
public import Theorem.Analysis.SpecialFunctions.Elliptic.Function

public section


namespace PeriodPair

/--
[Function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean)
-/
public theorem isLatticePeriodic_const_eq
-- given
  (L : PeriodPair)
  (c : ℂ) :
-- imply
  L.IsLatticePeriodic fun _ ↦ c :=
-- proof
  isLatticePeriodic_const L c

end PeriodPair

namespace PeriodPair

/--
[Function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean)
-/
public theorem IsEllipticFunction.const_eq
-- given
  (L : PeriodPair)
  (c : ℂ) :
-- imply
  L.IsEllipticFunction fun _ ↦ c :=
-- proof
  IsEllipticFunction.const L c

end PeriodPair

namespace PeriodPair

/--
[Function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean)
-/
public theorem IsEllipticFunction.add_eq
-- given
  (L : PeriodPair)
  (f g : ℂ → ℂ)
  (hf : L.IsEllipticFunction f)
  (hg : L.IsEllipticFunction g) :
-- imply
  L.IsEllipticFunction (f + g) :=
-- proof
  IsEllipticFunction.add hf hg

end PeriodPair

namespace PeriodPair

/--
[Function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean)
-/
public theorem IsEllipticFunction.mul_eq
-- given
  (L : PeriodPair)
  (f g : ℂ → ℂ)
  (hf : L.IsEllipticFunction f)
  (hg : L.IsEllipticFunction g) :
-- imply
  L.IsEllipticFunction (f * g) :=
-- proof
  IsEllipticFunction.mul hf hg

end PeriodPair


-- created on 2026-10-11
-- updated on 2026-10-26
