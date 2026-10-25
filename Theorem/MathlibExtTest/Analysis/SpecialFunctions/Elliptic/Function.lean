/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Elliptic/Function.lean -/


import Structure.Analysis.SpecialFunctions.Elliptic.Function
import Lemma.Complex.Function


example (L : PeriodPair) (c : ℂ) : L.IsEllipticFunction fun _ ↦ c :=
  PeriodPair.IsEllipticFunction.const L c

example (L : PeriodPair) : L.IsEllipticFunction L.weierstrassP :=
  ⟨L.meromorphic_weierstrassP, L.periodic_weierstrassP⟩

example {L : PeriodPair} {f g : ℂ → ℂ}
    (hf : L.IsEllipticFunction f) (hg : L.IsEllipticFunction g) :
    L.IsEllipticFunction (f + g) :=
  hf.add hg

