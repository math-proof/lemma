import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicStripCauchyFirstOrder
open Metric Set


/--
[isingFermionic_verticalOscillation_cauchy_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFirstOrder.lean)
-/
@[path]
private lemma isingFermionic_verticalOscillation_cauchy_first_eq
  {c : Complex}
  {d C : Real}
-- given
  (Phi : Complex -> Complex)
  (hd : 0 < d)
  (hC : 0 < C)
  (hPhi : DifferentiableOn Complex Phi (ball c d))
  (hosc : forall z, z ∈ ball c d -> |(Phi z).im - (Phi c).im| <= C) :
-- imply
  ‖iteratedDeriv 1 Phi c‖ <= 4 * C / d := by
-- proof
  apply isingFermionic_verticalOscillation_cauchy_first Phi c d C hd hC hPhi hosc

/--
[isingFermionic_norm_fderiv_real_im_le_iteratedDeriv_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFirstOrder.lean)
-/
@[path]
private lemma isingFermionic_norm_fderiv_real_im_le_iteratedDeriv_first_eq
  {c : Complex}
-- given
  (Phi : Complex -> Complex)
  (hPhi : ContDiffAt Complex 1 Phi c) :
-- imply
  ‖fderiv Real (fun u => (Phi u).im) c‖ <= ‖iteratedDeriv 1 Phi c‖ := by
-- proof
  apply isingFermionic_norm_fderiv_real_im_le_iteratedDeriv_first Phi c hPhi

/--
[isingFermionic_verticalOscillation_im_fderiv_le_on_halfBall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFirstOrder.lean)
-/
@[path]
private lemma isingFermionic_verticalOscillation_im_fderiv_le_on_halfBall_eq
  {c : Complex}
  {d C : Real}
-- given
  (Phi : Complex -> Complex)
  (hd : 0 < d)
  (hC : 0 < C)
  (hPhi : DifferentiableOn Complex Phi (ball c d))
  (hosc : forall z, z ∈ ball c d -> forall w, w ∈ ball c d -> |(Phi z).im - (Phi w).im| <= C) :
-- imply
  forall w, w ∈ ball c (d / 2) -> ‖fderiv Real (fun u => (Phi u).im) w‖ <= 8 * C / d := by
-- proof
  apply isingFermionic_verticalOscillation_im_fderiv_le_on_halfBall Phi c d C hd hC hPhi hosc

/--
[isingFermionic_verticalOscillation_lipschitzOn_carrier_of_balls](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFirstOrder.lean)
-/
@[path]
private lemma isingFermionic_verticalOscillation_lipschitzOn_carrier_of_balls_eq
  {K : Set Complex}
  {d C : Real}
-- given
  (Phi : Complex -> Complex)
  (hd : 0 < d)
  (hC : 0 < C)
  (hPhi : forall c, c ∈ K -> DifferentiableOn Complex Phi (ball c d))
  (hoscBall : forall c, c ∈ K -> forall z, z ∈ ball c d -> forall w, w ∈ ball c d -> |(Phi z).im - (Phi w).im| <= C)
  (hoscCarrier : forall z, z ∈ K -> forall w, w ∈ K -> |(Phi z).im - (Phi w).im| <= C) :
-- imply
  LipschitzOnWith ⟨8 * C / d, by positivity⟩ (fun z => (Phi z).im) K := by
-- proof
  apply isingFermionic_verticalOscillation_lipschitzOn_carrier_of_balls Phi K d C hd hC hPhi hoscBall hoscCarrier

/--
[isingFermionic_unitStrip_lipschitzOn_carrier_of_balls](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFirstOrder.lean)
-/
@[path]
private lemma isingFermionic_unitStrip_lipschitzOn_carrier_of_balls_eq
  {K : Set Complex}
  {d : Real}
-- given
  (Phi : Complex -> Complex)
  (hd : 0 < d)
  (hPhi : forall c, c ∈ K -> DifferentiableOn Complex Phi (ball c d))
  (hrangeBall : forall c, c ∈ K -> forall z, z ∈ ball c d -> 0 <= (Phi z).im /\ (Phi z).im <= 1)
  (hrangeCarrier : forall z, z ∈ K -> 0 <= (Phi z).im /\ (Phi z).im <= 1) :
-- imply
  LipschitzOnWith ⟨8 / d, by positivity⟩ (fun z => (Phi z).im) K := by
-- proof
  apply isingFermionic_unitStrip_lipschitzOn_carrier_of_balls Phi K d hd hPhi hrangeBall hrangeCarrier


-- created on 2026-10-23
