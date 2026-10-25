import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetDiscreteContraction
open Finset StatMech StatMech.FrontierD


/--
[abs_empiricalContinuousOffsetKernel_mul_le_of_zeroMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetDiscreteContraction.lean)
-/
@[path]
private lemma abs_empiricalContinuousOffsetKernel_mul_le_of_zeroMass_eq :
-- imply
  ∀ {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N) {p : Fin n → Real} {rho e : Fin n → Real} {i : Fin n} {E rowBound reciprocalMass : Real} (hrho : ∀ j, 0 < rho j) (hE : 0 ≤ E) (he : ∀ j, |e j| ≤ E) (hmass : (1 / (N : Real)) * ∑ j, e j / (sixVertexRootDensityWeight c (p j) * rho j) = 0) (hrow : (1 / (N : Real)) * ∑ j, sixVertexContinuousOffsetKernel c (p i) (p j) / rho j ≤ rowBound) (hreciprocal : reciprocalMass ≤ (1 / (N : Real)) * ∑ j, 1 / (sixVertexRootDensityWeight c (p j) * rho j)), |(1 / (N : Real)) * ∑ j, sixVertexContinuousOffsetKernel c (p i) (p j) / rho j * e j| ≤ (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass) * E := by
-- proof
  apply StatMech.FrontierD.abs_empiricalContinuousOffsetKernel_mul_le_of_zeroMass


-- created on 2026-10-23
