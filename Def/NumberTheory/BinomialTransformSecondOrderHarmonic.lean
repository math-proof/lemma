/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BinomialTransformSecondOrderHarmonic.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal


namespace MetaMathlibExt

noncomputable def H1 (n : ℕ) : ℂ := ∑ i ∈ Finset.Icc 1 n, (1 : ℂ) / (i : ℂ)

noncomputable def LHSstar (n : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 n, (-1 : ℂ) ^ (j - 1)
    * ((Finset.range j).prod (fun i => s + (n : ℂ) - (i : ℂ))
      / ((((Nat.factorial j : ℕ))) : ℂ)) / (j : ℂ)

noncomputable def Sstar (n : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 n, ((-1 : ℂ) ^ k
    * ((Finset.range (k - 1)).prod (fun i => s + (k : ℂ) - 1 - (i : ℂ))
      / ((((Nat.factorial (k - 1) : ℕ))) : ℂ)))
    / ((k : ℂ) ^ 2 * ((((n.choose k : ℕ))) : ℂ))

noncomputable def Qpoly (n j : ℕ) : Polynomial ℂ :=
  Polynomial.C (((-1 : ℂ) ^ (j - 1)) / (j : ℂ))
    * ((Finset.range j).prod (fun i => Polynomial.X + Polynomial.C ((n : ℂ) - (i : ℂ)))
      * Polynomial.C ((((Nat.factorial j : ℕ)) : ℂ)⁻¹))

noncomputable def Rpoly (n k : ℕ) : Polynomial ℂ :=
  Polynomial.C (((-1 : ℂ) ^ k) / ((k : ℂ) ^ 2 * ((((n.choose k : ℕ))) : ℂ)))
    * ((Finset.range (k - 1)).prod
        (fun i => Polynomial.X + Polynomial.C ((k : ℂ) - 1 - (i : ℂ)))
      * Polynomial.C ((((Nat.factorial (k - 1) : ℕ)) : ℂ)⁻¹))

noncomputable def Presid (n : ℕ) : Polynomial ℂ :=
  (∑ j ∈ Finset.Icc 1 n, Qpoly n j)
    + Polynomial.X * (∑ k ∈ Finset.Icc 1 n, Rpoly n k)
    - Polynomial.C (H1 n)

end MetaMathlibExt
