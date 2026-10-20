import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.GeneralLinearGroupExponent
open MetaMathlibExt


/--
[to](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GeneralLinearGroupExponent.lean)
-/
@[path]
private lemma to_eq
  {1939}
  {1948} :
-- imply
  ℕ) (hp : p.Prime) (hm : 0 < m) :
    Monoid.exponent (Matrix.GeneralLinearGroup (Fin m) (ZMod p)) =
    p ^ Nat.clog p m * (Finset.range m).lcm (fun i => p ^ (i + 1) - 1) ∧
    ((p ^ Nat.clog p m * (Finset.range m).lcm (fun i => p ^ (i + 1) - 1) : ℕ) : ℤ) =
    (p : ℤ) ^ Nat.clog p m *
    ∏ k ∈ Finset.Icc 1 m, (Polynomial.cyclotomic k ℤ).eval (p : ℤ) := by
-- proof
  apply MetaMathlibExt.to 1939 1948

/--
[generalLinearGroup_exponent_eq_lcm_eq_cyclotomicProduct](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GeneralLinearGroupExponent.lean)
-/
@[path]
private lemma generalLinearGroup_exponent_eq_lcm_eq_cyclotomicProduct_eq
  {p m : ℕ}
-- given
  (hp : p.Prime)
  (hm : 0 < m) :
-- imply
  Monoid.exponent (Matrix.GeneralLinearGroup (Fin m) (ZMod p)) =
    p ^ Nat.clog p m * (Finset.range m).lcm (fun i => p ^ (i + 1) - 1) ∧
    ((p ^ Nat.clog p m * (Finset.range m).lcm (fun i => p ^ (i + 1) - 1) : ℕ) : ℤ) =
    (p : ℤ) ^ Nat.clog p m *
    ∏ k ∈ Finset.Icc 1 m, (Polynomial.cyclotomic k ℤ).eval (p : ℤ) := by
-- proof
  apply MetaMathlibExt.generalLinearGroup_exponent_eq_lcm_eq_cyclotomicProduct p m hp hm


-- created on 2026-10-20
