import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterThreeBridgeClosure
open Finset SimpleGraph StatMech StatMech.Ising


/--
[threeBridge_sum_mul_sum_le_two_add_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridge_sum_mul_sum_le_two_add_three_eq
  [Fintype V]
  [DecidableEq V]
  {u₁ u₂ u₃ v₁₂ v₁₃ v₂₃ c : Real}
-- given
  (hu₁ : 0 <= u₁)
  (hu₂ : 0 <= u₂)
  (hu₃ : 0 <= u₃)
  (hv₁₂ : v₁₂ <= 1)
  (hv₁₃ : v₁₃ <= 1)
  (hv₂₃ : v₂₃ <= 1)
  (hop₁ : u₁ * v₂₃ <= c)
  (hop₂ : u₂ * v₁₃ <= c)
  (hop₃ : u₃ * v₁₂ <= c) :
-- imply
  (u₁ + u₂ + u₃) * (v₁₂ + v₁₃ + v₂₃) <= 2 * (u₁ + u₂ + u₃) + 3 * c := by
-- proof
  apply StatMech.Ising.threeBridge_sum_mul_sum_le_two_add_three hu₁ hu₂ hu₃ hv₁₂ hv₁₃ hv₂₃ hop₁ hop₂ hop₃

/--
[threeBridge_ghsSquare_le_firstBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridge_ghsSquare_le_firstBound_eq
  [Fintype V]
  [DecidableEq V]
  {x y z p q s : Real}
-- given
  (hx0 : 0 <= x)
  (hy0 : 0 <= y)
  (hz0 : 0 <= z)
  (hx1 : x <= 1)
  (hy1 : y <= 1)
  (hz1 : z <= 1)
  (hp : x * y <= p)
  (hq : x * z <= q)
  (hs : y * z <= s) :
-- imply
  3 * (x * s + y * q + z * p - 2 * x * y * z) ^ 2 <= (x ^ 2 + y ^ 2 + z ^ 2) + 3 * (x ^ 2 + y ^ 2 + z ^ 2) * (p ^ 2 + q ^ 2 + s ^ 2) - (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 := by
-- proof
  apply StatMech.Ising.threeBridge_ghsSquare_le_firstBound hx0 hy0 hz0 hx1 hy1 hz1 hp hq hs

/--
[threeBridge_bernsteinOne_nonpos_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridge_bernsteinOne_nonpos_of_bounds_eq
  [Fintype V]
  [DecidableEq V]
  {a b c : Real}
-- given
  (ha0 : 0 <= a)
  (hb0 : 0 <= b)
  (hzero : a ^ 3 - 3 * a * b - a + 3 * c <= 0)
  (hdis : 0 <= 1 - a + b - c)
  (hpair : 2 * a <= 3 + b) :
-- imply
  (2 * a ^ 3 + 2 * a ^ 2 * c - a * b ^ 2 - 5 * a * b - 2 * a + b * c + 3 * c) / 2 <= 0 := by
-- proof
  apply StatMech.Ising.threeBridge_bernsteinOne_nonpos_of_bounds ha0 hb0 hzero hdis hpair

/--
[threeBridge_two_sqsum_le_three_add_pairSqsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridge_two_sqsum_le_three_add_pairSqsum_eq
  [Fintype V]
  [DecidableEq V]
  {x y z p q s : Real}
-- given
  (hx0 : 0 <= x)
  (hy0 : 0 <= y)
  (hz0 : 0 <= z)
  (hx1 : x <= 1)
  (hy1 : y <= 1)
  (hz1 : z <= 1)
  (hp : x * y <= p)
  (hq : x * z <= q)
  (hs : y * z <= s) :
-- imply
  2 * (x ^ 2 + y ^ 2 + z ^ 2) <= 3 + (p ^ 2 + q ^ 2 + s ^ 2) := by
-- proof
  apply StatMech.Ising.threeBridge_two_sqsum_le_three_add_pairSqsum hx0 hy0 hz0 hx1 hy1 hz1 hp hq hs

/--
[threeBridge_bernsteinTwo_nonpos_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridge_bernsteinTwo_nonpos_of_bounds_eq
  [Fintype V]
  [DecidableEq V]
  {a b c : Real}
-- given
  (ha0 : 0 <= a)
  (hb0 : 0 <= b)
  (hc0 : 0 <= c)
  (hb3 : b <= 3)
  (hc1 : c <= 1)
  (hzero : a ^ 3 - 3 * a * b - a + 3 * c <= 0)
  (hdis : 0 <= 1 - a + b - c)
  (hpair : 2 * a <= 3 + b) :
-- imply
  -(a ^ 3 * b - 6 * a ^ 3 + 3 * a ^ 2 * b * c - 13 * a ^ 2 * c - a * b ^ 3 + 3 * a * b ^ 2 + 12 * a * b - 9 * a * c ^ 2 + 6 * a + b ^ 2 * c + 3 * b * c) / 6 <= 0 := by
-- proof
  apply StatMech.Ising.threeBridge_bernsteinTwo_nonpos_of_bounds ha0 hb0 hc0 hb3 hc1 hzero hdis hpair

/--
[threeBridge_pairTriangle_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridge_pairTriangle_core_eq
  [Fintype V]
  [DecidableEq V]
  {X Y Z : Real}
-- given
  (hX0 : 0 <= X)
  (hY0 : 0 <= Y)
  (hZ0 : 0 <= Z)
  (hXY : X * Y <= Z)
  (hXZ : X * Z <= Y)
  (hYZ : Y * Z <= X) :
-- imply
  (X + Y + Z - 1) * (X * Y + X * Z + Y * Z) <= (X + Y + Z + 3) * (X * Y * Z) := by
-- proof
  apply StatMech.Ising.threeBridge_pairTriangle_core hX0 hY0 hZ0 hXY hXZ hYZ

/--
[threeBridge_sum_mul_sum_le_one_add_c](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridge_sum_mul_sum_le_one_add_c_eq
  [Fintype V]
  [DecidableEq V]
  {u₁ u₂ u₃ X Y Z c : Real}
-- given
  (hu₁0 : 0 <= u₁)
  (hu₂0 : 0 <= u₂)
  (hu₃0 : 0 <= u₃)
  (hX0 : 0 <= X)
  (hY0 : 0 <= Y)
  (hZ0 : 0 <= Z)
  (hX1 : X <= 1)
  (hY1 : Y <= 1)
  (hZ1 : Z <= 1)
  (hc0 : 0 <= c)
  (hXY : X * Y <= Z)
  (hXZ : X * Z <= Y)
  (hYZ : Y * Z <= X)
  (hop₁ : u₁ * Z <= c)
  (hop₂ : u₂ * Y <= c)
  (hop₃ : u₃ * X <= c) :
-- imply
  (u₁ + u₂ + u₃) * (X + Y + Z) <= (u₁ + u₂ + u₃) + c * (X + Y + Z) + 3 * c := by
-- proof
  apply StatMech.Ising.threeBridge_sum_mul_sum_le_one_add_c hu₁0 hu₂0 hu₃0 hX0 hY0 hZ0 hX1 hY1 hZ1 hc0 hXY hXZ hYZ hop₁ hop₂ hop₃

/--
[threeBridge_singleton_mul_opposite_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridge_singleton_mul_opposite_sq_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  (expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 * (expJ G.edgeFinset J hf (fun s => spin s y * spin s z)) ^ 2 <= (expJ G.edgeFinset J hf (fun s => spin s x * (spin s y * spin s z))) ^ 2 := by
-- proof
  apply StatMech.Ising.threeBridge_singleton_mul_opposite_sq_le G J hf hJ hhf hxy hxz hyz

/--
[threeBridge_pair_mul_pair_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridge_pair_mul_pair_sq_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  (expJ G.edgeFinset J hf (fun s => spin s x * spin s y)) ^ 2 * (expJ G.edgeFinset J hf (fun s => spin s x * spin s z)) ^ 2 <= (expJ G.edgeFinset J hf (fun s => spin s y * spin s z)) ^ 2 := by
-- proof
  apply StatMech.Ising.threeBridge_pair_mul_pair_sq_le G J hf hJ hhf hxy hxz hyz

/--
[threeBridge_ab_le_two_a_add_three_c](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridge_ab_le_two_a_add_three_c_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  threeBridgeOneCoeff G J hf x y z * threeBridgeTwoCoeff G J hf x y z <= 2 * threeBridgeOneCoeff G J hf x y z + 3 * threeBridgeThreeCoeff G J hf x y z := by
-- proof
  apply StatMech.Ising.threeBridge_ab_le_two_a_add_three_c G J hf hJ hhf hxy hxz hyz

/--
[threeBridge_ab_le_a_add_bc_add_three_c](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridge_ab_le_a_add_bc_add_three_c_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  threeBridgeOneCoeff G J hf x y z * threeBridgeTwoCoeff G J hf x y z <= threeBridgeOneCoeff G J hf x y z + threeBridgeThreeCoeff G J hf x y z * threeBridgeTwoCoeff G J hf x y z + 3 * threeBridgeThreeCoeff G J hf x y z := by
-- proof
  apply StatMech.Ising.threeBridge_ab_le_a_add_bc_add_three_c G J hf hJ hhf hxy hxz hyz

/--
[threeBridgeVarianceSkewBernsteinCoeff_zero_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridgeVarianceSkewBernsteinCoeff_zero_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  threeBridgeVarianceSkewBernsteinCoeff (threeBridgeOneCoeff G J hf x y z) (threeBridgeTwoCoeff G J hf x y z) (threeBridgeThreeCoeff G J hf x y z) 0 <= 0 := by
-- proof
  apply StatMech.Ising.threeBridgeVarianceSkewBernsteinCoeff_zero_nonpos G J hf hJ hhf hxy hxz hyz

/--
[threeBridgeVarianceSkewBernsteinCoeff_one_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridgeVarianceSkewBernsteinCoeff_one_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  threeBridgeVarianceSkewBernsteinCoeff (threeBridgeOneCoeff G J hf x y z) (threeBridgeTwoCoeff G J hf x y z) (threeBridgeThreeCoeff G J hf x y z) 1 <= 0 := by
-- proof
  apply StatMech.Ising.threeBridgeVarianceSkewBernsteinCoeff_one_nonpos G J hf hJ hhf hxy hxz hyz

/--
[threeBridgeVarianceSkewBernsteinCoeff_two_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridgeVarianceSkewBernsteinCoeff_two_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  threeBridgeVarianceSkewBernsteinCoeff (threeBridgeOneCoeff G J hf x y z) (threeBridgeTwoCoeff G J hf x y z) (threeBridgeThreeCoeff G J hf x y z) 2 <= 0 := by
-- proof
  apply StatMech.Ising.threeBridgeVarianceSkewBernsteinCoeff_two_nonpos G J hf hJ hhf hxy hxz hyz

/--
[threeBridgeVarianceSkewBernsteinCoeff_three_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridgeVarianceSkewBernsteinCoeff_three_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  threeBridgeVarianceSkewBernsteinCoeff (threeBridgeOneCoeff G J hf x y z) (threeBridgeTwoCoeff G J hf x y z) (threeBridgeThreeCoeff G J hf x y z) 3 <= 0 := by
-- proof
  apply StatMech.Ising.threeBridgeVarianceSkewBernsteinCoeff_three_nonpos G J hf hJ hhf hxy hxz hyz

/--
[threeBridgeVarianceSkewBernsteinCoeff_four_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridgeVarianceSkewBernsteinCoeff_four_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  threeBridgeVarianceSkewBernsteinCoeff (threeBridgeOneCoeff G J hf x y z) (threeBridgeTwoCoeff G J hf x y z) (threeBridgeThreeCoeff G J hf x y z) 4 <= 0 := by
-- proof
  apply StatMech.Ising.threeBridgeVarianceSkewBernsteinCoeff_four_nonpos G J hf hJ hhf hxy hxz hyz

/--
[threeBridgeVarianceSkewBernsteinCoeff_all_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma threeBridgeVarianceSkewBernsteinCoeff_all_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
  {i : Fin 5}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  threeBridgeVarianceSkewBernsteinCoeff (threeBridgeOneCoeff G J hf x y z) (threeBridgeTwoCoeff G J hf x y z) (threeBridgeThreeCoeff G J hf x y z) i <= 0 := by
-- proof
  apply StatMech.Ising.threeBridgeVarianceSkewBernsteinCoeff_all_nonpos G J hf hJ hhf hxy hxz hyz i

/--
[replicaBridgeVariance_threeBridgeSites_le_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma replicaBridgeVariance_threeBridgeSites_le_neg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z)
  (hr : 0 <= r) :
-- imply
  replicaBridgeVariance G J hf (threeBridgeSites x y z) r <= replicaBridgeVariance G J hf (threeBridgeSites x y z) (-r) := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_threeBridgeSites_le_neg G J hf hJ hhf hxy hxz hyz r hr

/--
[replicaBridgeFreeEnergy_threeBridgeSites_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeClosure.lean)
-/
@[path]
private lemma replicaBridgeFreeEnergy_threeBridgeSites_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z)
  (hr : 0 <= r) :
-- imply
  replicaBridgeFreeEnergy G J hf (threeBridgeSites x y z) r <= 2 * r * threeBridgeOneCoeff G J hf x y z := by
-- proof
  apply StatMech.Ising.replicaBridgeFreeEnergy_threeBridgeSites_le G J hf hJ hhf hxy hxz hyz r hr


-- created on 2026-10-23
