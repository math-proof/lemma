/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Elliptic/Function.lean -/
module

public import Structure.Analysis.SpecialFunctions.Elliptic.Function
public import Theorem.Complex.Function

public section

example (L : PeriodPair) (c : ℂ) : L.IsEllipticFunction fun _ ↦ c :=
  PeriodPair.IsEllipticFunction.const L c

example (L : PeriodPair) : L.IsEllipticFunction L.weierstrassP :=
  ⟨L.meromorphic_weierstrassP, L.periodic_weierstrassP⟩

example {L : PeriodPair} {f g : ℂ → ℂ}
    (hf : L.IsEllipticFunction f) (hg : L.IsEllipticFunction g) :
    L.IsEllipticFunction (f + g) :=
  hf.add hg

