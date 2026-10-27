import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part6
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexForwardInterlaced_iff_positions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexForwardInterlaced_iff_positions_eq
  {N n : ℕ}
  {x y : SixVertexSector N n} :
-- imply
  SixVertexForwardInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) ↔ SixVertexPositionsForwardInterlaced x y := by
-- proof
  apply StatMech.FrontierD.sixVertexForwardInterlaced_iff_positions x y

/--
[sixVertexBethePairFactor_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexBethePairFactor_phase_eq
  {c p q : ℝ} :
-- imply
  sixVertexBethePairFactor c (sixVertexBethePhase p) (sixVertexBethePhase q) = sixVertexBethePhase p * (sixVertexBethePhase (-p) + sixVertexBethePhase q - 2 * sixVertexDelta c) := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePairFactor_phase c p q

/--
[sixVertexScatteringDenominator_eq_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexScatteringDenominator_eq_phase_eq
  {c p q : ℝ} :
-- imply
  sixVertexScatteringDenominator c p q = sixVertexBethePhase p + sixVertexBethePhase (-q) - 2 * sixVertexDelta c := by
-- proof
  apply StatMech.FrontierD.sixVertexScatteringDenominator_eq_phase c p q

/--
[sixVertexBethePairFactor_eq_phase_mul_conj_denominator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexBethePairFactor_eq_phase_mul_conj_denominator_eq
  {c p q : ℝ} :
-- imply
  sixVertexBethePairFactor c (sixVertexBethePhase p) (sixVertexBethePhase q) = sixVertexBethePhase p * star (sixVertexScatteringDenominator c p q) := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePairFactor_eq_phase_mul_conj_denominator c p q

/--
[sixVertexBethePairFactor_swap_eq_phase_mul_denominator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexBethePairFactor_swap_eq_phase_mul_denominator_eq
  {c p q : ℝ} :
-- imply
  sixVertexBethePairFactor c (sixVertexBethePhase q) (sixVertexBethePhase p) = sixVertexBethePhase q * sixVertexScatteringDenominator c p q := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePairFactor_swap_eq_phase_mul_denominator c p q

/--
[sixVertexBethePairFactor_phase_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexBethePairFactor_phase_ne_zero_eq
  {c : ℝ}
  {p q : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBethePairFactor c (sixVertexBethePhase p) (sixVertexBethePhase q) ≠ 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePairFactor_phase_ne_zero hc p q

/--
[sixVertexBethePhase_sub_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexBethePhase_sub_mul_eq
  {p q : ℝ} :
-- imply
  Complex.exp (Complex.I * (p - q)) * sixVertexBethePhase q = sixVertexBethePhase p := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePhase_sub_mul p q

/--
[sixVertexBethePhase_injective_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexBethePhase_injective_on_Ioo_eq :
-- imply
  Set.InjOn sixVertexBethePhase (Set.Ioo (-Real.pi) Real.pi) := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePhase_injective_on_Ioo

/--
[SixVertexOpenRootSimplex.phase_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma phase_injective_eq
  {n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hp : SixVertexOpenRootSimplex p) :
-- imply
  Function.Injective fun j => sixVertexBethePhase (p j) := by
-- proof
  apply StatMech.FrontierD.SixVertexOpenRootSimplex.phase_injective hp

/--
[SixVertexOpenRootSimplex.ne_zero_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma ne_zero_of_even_eq
  {k : ℕ}
  {p : Fin (k + k) → ℝ}
  {j : Fin (k + k)}
-- given
  (hp : SixVertexOpenRootSimplex p) :
-- imply
  p j ≠ 0 := by
-- proof
  apply StatMech.FrontierD.SixVertexOpenRootSimplex.ne_zero_of_even hp j

/--
[SixVertexOpenRootSimplex.phase_ne_one_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma phase_ne_one_of_even_eq
  {k : ℕ}
  {p : Fin (k + k) → ℝ}
  {j : Fin (k + k)}
-- given
  (hp : SixVertexOpenRootSimplex p) :
-- imply
  sixVertexBethePhase (p j) ≠ 1 := by
-- proof
  apply StatMech.FrontierD.SixVertexOpenRootSimplex.phase_ne_one_of_even hp j

/--
[sixVertexBethePairFactor_exchange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexBethePairFactor_exchange_eq
  {c : ℝ}
  {p q : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  Complex.exp (-Complex.I * sixVertexTheta c p q) * sixVertexBethePairFactor c (sixVertexBethePhase q) (sixVertexBethePhase p) = sixVertexBethePairFactor c (sixVertexBethePhase p) (sixVertexBethePhase q) := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePairFactor_exchange hc p q

/--
[sixVertexBethePhase_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexBethePhase_pow_eq
  {N : ℕ}
  {p : ℝ} :
-- imply
  sixVertexBethePhase p ^ N = Complex.exp (Complex.I * ((N : ℝ) * p)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePhase_pow N p

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.pairFactor_periodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma pairFactor_periodic_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
  {j : Fin n}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N n p) :
-- imply
  sixVertexBethePhase (p j) ^ N * (∏ k, sixVertexBethePairFactor c (sixVertexBethePhase (p k)) (sixVertexBethePhase (p j))) = (-1 : ℂ) ^ (n - 1) * ∏ k, sixVertexBethePairFactor c (sixVertexBethePhase (p j)) (sixVertexBethePhase (p k)) := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.pairFactor_periodic hc hp j

/--
[sixVertexBetheAmplitude_eq_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexBetheAmplitude_eq_source_eq
  {n : ℕ}
  {c : ℝ}
  {p : Fin n → ℝ}
  {σ : Equiv.Perm (Fin n)} :
-- imply
  sixVertexBetheAmplitude c p σ = (((Equiv.Perm.sign σ : ℤ) : ℂ)) * ∏ k, ∏ l ∈ Finset.Ioi k, sixVertexBethePhase (p (σ k)) * (sixVertexBethePhase (-(p (σ k))) + sixVertexBethePhase (p (σ l)) - 2 * sixVertexDelta c) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheAmplitude_eq_source c p σ

/--
[sixVertexBethePairProduct_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexBethePairProduct_ne_zero_eq
  {c : ℝ}
  {n : ℕ}
  {p : Fin n → ℝ}
  {σ : Equiv.Perm (Fin n)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBethePairProduct c p σ ≠ 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePairProduct_ne_zero hc p σ

/--
[sixVertexBetheAmplitude_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexBetheAmplitude_ne_zero_eq
  {c : ℝ}
  {n : ℕ}
  {p : Fin n → ℝ}
  {σ : Equiv.Perm (Fin n)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBetheAmplitude c p σ ≠ 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheAmplitude_ne_zero hc p σ

/--
[sixVertexSectorTransferComplex_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexSectorTransferComplex_apply_eq
  {N n : ℕ}
  {c : ℝ}
  {x y : SixVertexSector N n} :
-- imply
  sixVertexSectorTransferComplex N n c x y = (sixVertexSectorTransfer N n c x y : ℂ) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferComplex_apply N n c x y

/--
[sixVertexSectorTransferComplex_mulVec_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexSectorTransferComplex_mulVec_apply_eq
  {N n : ℕ}
  {c : ℝ}
  {v : SixVertexSector N n → ℂ}
  {x : SixVertexSector N n} :
-- imply
  (sixVertexSectorTransferComplex N n c).mulVec v x = ∑ y, (sixVertexSectorTransfer N n c x y : ℂ) * v y := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferComplex_mulVec_apply N n c v x

/--
[sixVertexSectorRowDistance_eq_card_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexSectorRowDistance_eq_card_symmDiff_eq
  {N n : ℕ}
  {x y : SixVertexSector N n} :
-- imply
  sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) = ((x : Finset (Fin N)) ∆ (y : Finset (Fin N))).card := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorRowDistance_eq_card_symmDiff x y

/--
[sixVertexSectorRowDistance_eq_two_mul_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexSectorRowDistance_eq_two_mul_sdiff_eq
  {N n : ℕ}
  {x y : SixVertexSector N n} :
-- imply
  sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) = 2 * ((x : Finset (Fin N)) \ (y : Finset (Fin N))).card := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorRowDistance_eq_two_mul_sdiff x y

/--
[sixVertexSectorTransferComplex_mulVec_eq_interlacedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexSectorTransferComplex_mulVec_eq_interlacedSum_eq
  {N n : ℕ}
  {c : ℝ}
  {v : SixVertexSector N n → ℂ}
  {x : SixVertexSector N n} :
-- imply
  (sixVertexSectorTransferComplex N n c).mulVec v x = 2 * v x + ∑ y ∈ (Finset.univ.erase x), if SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) then (c : ℂ) ^ sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) * v y else 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferComplex_mulVec_eq_interlacedSum N n c v x

/--
[prod_sixVertexPairedRootFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma prod_sixVertexPairedRootFamily_eq
  {k : ℕ}
  {p : Fin k → ℝ}
  {f : ℝ → ℂ} :
-- imply
  (∏ i, f (sixVertexPairedRootFamily p i)) = (∏ j, f (p j)) * ∏ j, f (-p j) := by
-- proof
  apply StatMech.FrontierD.prod_sixVertexPairedRootFamily p f

/--
[sixVertexBetheEigenvalueCandidate_paired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexBetheEigenvalueCandidate_paired_eq
  {k : ℕ}
  {c : ℝ}
  {p : Fin k → ℝ} :
-- imply
  sixVertexBetheEigenvalueCandidate c (sixVertexPairedRootFamily p) = sixVertexSymmetricBetheEigenvalueCandidate c p := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheEigenvalueCandidate_paired c p

/--
[sixVertexBethePairProduct_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexBethePairProduct_zero_eq
  {c : ℝ}
  {p : Fin 0 → ℝ}
  {σ : Equiv.Perm (Fin 0)} :
-- imply
  sixVertexBethePairProduct c p σ = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePairProduct_zero c p σ

/--
[sixVertexBetheAmplitude_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexBetheAmplitude_zero_eq
  {c : ℝ}
  {p : Fin 0 → ℝ}
  {σ : Equiv.Perm (Fin 0)} :
-- imply
  sixVertexBetheAmplitude c p σ = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheAmplitude_zero c p σ

/--
[sixVertexBetheEigenvalueCandidate_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexBetheEigenvalueCandidate_zero_eq
  {c : ℝ}
  {p : Fin 0 → ℝ} :
-- imply
  sixVertexBetheEigenvalueCandidate c p = 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheEigenvalueCandidate_zero c p

/--
[sixVertexCoordinateBetheEigenrelation_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean)
-/
@[path]
private lemma sixVertexCoordinateBetheEigenrelation_zero_eq
  {N : ℕ}
  {c : ℝ}
  {p : Fin 0 → ℝ} :
-- imply
  SixVertexCoordinateBetheEigenrelation (N := N) c p := by
-- proof
  apply StatMech.FrontierD.sixVertexCoordinateBetheEigenrelation_zero N c p


-- created on 2026-10-23
