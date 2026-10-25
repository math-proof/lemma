import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterSingleBondUpper.Part2
open Set StatMech StatMech.Ising


/--
[hasDerivAt_tanh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBondUpper.lean)
-/
@[path]
private lemma hasDerivAt_tanh_eq
  {x : Real} :
-- imply
  HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
-- proof
  apply StatMech.Ising.hasDerivAt_tanh x

/--
[antitoneOn_tanh_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBondUpper.lean)
-/
@[path]
private lemma antitoneOn_tanh_div_eq :
-- imply
  AntitoneOn (fun x : Real => Real.tanh x / x) (Ioi 0) := by
-- proof
  apply StatMech.Ising.antitoneOn_tanh_div

/--
[mul_tanh_le_tanh_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBondUpper.lean)
-/
@[path]
private lemma mul_tanh_le_tanh_mul_eq
  {a x : Real}
-- given
  (ha0 : 0 <= a)
  (ha1 : a <= 1)
  (hx : 0 <= x) :
-- imply
  a * Real.tanh x <= Real.tanh (a * x) := by
-- proof
  apply StatMech.Ising.mul_tanh_le_tanh_mul ha0 ha1 hx

/--
[artanh_mul_tanh_le_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBondUpper.lean)
-/
@[path]
private lemma artanh_mul_tanh_le_mul_eq
  {a x : Real}
-- given
  (ha0 : 0 <= a)
  (ha1 : a <= 1)
  (hx : 0 <= x) :
-- imply
  Real.artanh (a * Real.tanh x) <= a * x := by
-- proof
  apply StatMech.Ising.artanh_mul_tanh_le_mul ha0 ha1 hx

/--
[singleBondInterfaceFreeEnergy_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBondUpper.lean)
-/
@[path]
private lemma singleBondInterfaceFreeEnergy_le_eq
  {K m1 m2 : Real}
-- given
  (hK : 0 <= K)
  (hm10 : 0 <= m1)
  (hm11 : m1 <= 1)
  (hm20 : 0 <= m2)
  (hm21 : m2 <= 1) :
-- imply
  singleBondInterfaceFreeEnergy K m1 m2 <= 2 * K * (m1 * m2) := by
-- proof
  apply StatMech.Ising.singleBondInterfaceFreeEnergy_le hK hm10 hm11 hm20 hm21


-- created on 2026-10-23
