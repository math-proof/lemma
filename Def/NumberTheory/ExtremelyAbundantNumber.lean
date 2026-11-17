/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ExtremelyAbundantNumber.lean -/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MetaMathlibExt

/-- Extremely abundant number (concept `jis_term_5535518aa70e4c378d88a78e`,
source `jis_source_6854eacdc72e1e5a005b0055`, lines 200-219). -/
def IsExtremelyAbundantNumber (n : Nat) : Prop :=
  n = 10080 ∨
    (10080 < n ∧
      ∀ m : Nat, 10080 ≤ m → m < n →
        ((ArithmeticFunction.sigma 1 n : Nat) : Real) /
            ((n : Real) * Real.log (Real.log (n : Real))) >
          ((ArithmeticFunction.sigma 1 m : Nat) : Real) /
            ((m : Real) * Real.log (Real.log (m : Real))))

end MetaMathlibExt
