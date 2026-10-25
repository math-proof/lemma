/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/CubicResidueSymbol.lean -/

import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.Ideal.Basic


namespace MetaMathlibExt

open Ideal NumberField

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {3} ℚ K]

/-
Source: Peng Gao and Liangyi Zhao, "Ratios conjecture of cubic L-functions of prime
moduli," arXiv:2311.08626v3, Indagationes Mathematicae. Definition of cubic residue
symbol leg {·}{·}_3 for K = Q(ω), O_K = Z[ω], ω = hZeta.toInteger.
Bytes [25829,26379) of RatioconjcubicHeckeLfcnsPrim_031.tex.
-/

abbrev omega {zeta : K} (hZeta : IsPrimitiveRoot zeta 3) :
    NumberField.RingOfIntegers K :=
  hZeta.toInteger

end MetaMathlibExt
