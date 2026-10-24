import Mathlib
import sympy.Basic
import sympy.functions.special.elliptic.Function


namespace PeriodPair

/--
[Function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean)
-/
@[path]
lemma isLatticePeriodic_const
-- given
  (L : PeriodPair)
  (c : ℂ) :
-- imply
  L.IsLatticePeriodic fun _ ↦ c :=
-- proof
  fun _ _ ↦ rfl

end PeriodPair

namespace PeriodPair

/--
[Function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean)
-/
@[path]
lemma IsEllipticFunction.const
-- given
  (L : PeriodPair)
  (c : ℂ) :
-- imply
  L.IsEllipticFunction fun _ ↦ c :=
-- proof
  ⟨Meromorphic.const c, isLatticePeriodic_const L c⟩

end PeriodPair

/--
[Function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean)
-/
@[path]
lemma IsEllipticFunction.add
-- given
  (L : PeriodPair)
  (f g : ℂ → ℂ)
  (hf : L.IsEllipticFunction f)
  (hg : L.IsEllipticFunction g) :
-- imply
  L.IsEllipticFunction (f + g) :=
-- proof
  ⟨hf.meromorphic.add hg.meromorphic, fun ω ↦ (hf.periodic ω).add (hg.periodic ω)⟩


namespace PeriodPair

/--
[Function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Function.lean)
-/
@[path]
lemma IsEllipticFunction.mul
-- given
  (L : PeriodPair)
  (f g : ℂ → ℂ)
  (hf : L.IsEllipticFunction f)
  (hg : L.IsEllipticFunction g) :
-- imply
  L.IsEllipticFunction (f * g) :=
-- proof
  ⟨hf.meromorphic.mul hg.meromorphic, fun ω ↦ (hf.periodic ω).mul (hg.periodic ω)⟩

end PeriodPair


-- created on 2026-10-11
-- updated on 2026-10-23
