/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Cyclotomic/LehmerLaurentIdentity.lean -/

import Def.NumberTheory.Cyclotomic.RealCyclotomicPolynomial
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Def.NumberTheory.Cyclotomic.LehmerLaurentIdentity


namespace MetaMathlibExt

/-- `ℚ⟮s⟯`, the base field for the quadratic step, where `s = ζ + ζ⁻¹`. -/
noncomputable abbrev baseField (n : ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({zeta n + (zeta n)⁻¹} : Set ℂ)

end MetaMathlibExt
