import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
open StatMech StatMech.Universality


/--
[laterEndpointVerticalKernel_tail_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicOrderedEndpointConvolution.lean)
-/
@[path]
private lemma laterEndpointVerticalKernel_tail_le_eq
  {j N : Nat} :
-- imply
  (∑ l ∈ Finset.range N, (2 / ((j + l + 1 : Nat) : Real)) * (2 / Real.sqrt ((l + 2 : Nat) : Real))) <= 32 / Real.sqrt ((j + 1 : Nat) : Real) := by
-- proof
  apply StatMech.Universality.laterEndpointVerticalKernel_tail_le j N

/--
[orderedFarFirstEndpoint_swapped_convolution_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicOrderedEndpointConvolution.lean)
-/
@[path]
private lemma orderedFarFirstEndpoint_swapped_convolution_le_eq
  {T : Nat}
-- given
  (b : Nat -> Real)
  (hb0 : forall j, 0 <= b j) :
-- imply
  (∑ j ∈ Finset.range (T + 1), b j * (∑ l ∈ Finset.range (T - j), (2 / ((j + l + 1 : Nat) : Real)) * (2 / Real.sqrt ((l + 2 : Nat) : Real)))) <= 16 * (∑ j ∈ Finset.range (T + 1), (2 / Real.sqrt ((j + 1 : Nat) : Real)) * b j) := by
-- proof
  apply StatMech.Universality.orderedFarFirstEndpoint_swapped_convolution_le T b hb0

/--
[orderedFarFirstEndpoint_convolution_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicOrderedEndpointConvolution.lean)
-/
@[path]
private lemma orderedFarFirstEndpoint_convolution_le_eq
  {rho m T : Nat}
  {C : Real}
-- given
  (b v : Nat -> Real)
  (hρ : 0 < rho)
  (hρm : rho <= m)
  (hT : T <= rho * rho)
  (hC : 0 <= C)
  (hv0 : forall k, 0 <= v k)
  (hb : forall j, j <= T -> b j <= C * (j + 1 : Real) / (m : Real) ^ 5)
  (hvMass : (∑ k ∈ Finset.range (T + 1), v k) <= 1) :
-- imply
  (∑ k ∈ Finset.range (T + 1), v k * (∑ j ∈ Finset.range k, b j * (2 / Real.sqrt ((k - j + 1 : Nat) : Real)))) <= 32 * C / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.orderedFarFirstEndpoint_convolution_le rho m T C b v hρ hρm hT hC hv0 hb hvMass


-- created on 2026-10-23
