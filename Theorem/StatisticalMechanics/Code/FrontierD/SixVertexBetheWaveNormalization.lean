/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWaveNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedPerron.Part3
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem perm_fin_two_eq_id_or_swap (σ : Equiv.Perm (Fin 2)) :
    σ = 1 ∨ σ = Equiv.swap 0 1 := by
  by_cases h0 : σ 0 = 0
  · left
    apply Equiv.ext
    intro i
    fin_cases i
    · simpa using h0
    · have h1 : σ 1 = 1 := by
        apply Fin.eq_of_val_eq
        have hne : σ 1 ≠ 0 := by
          intro h
          exact Fin.zero_ne_one (σ.injective (h0.trans h.symm))
        omega
      exact h1
  · right
    apply Equiv.ext
    intro i
    fin_cases i
    · have hs0 : σ 0 = 1 := by
        apply Fin.eq_of_val_eq
        have := (σ 0).isLt
        have hz : (σ 0).val ≠ 0 := by
          intro hz
          exact h0 (Fin.eq_of_val_eq hz)
        omega
      exact hs0
    · have hs0 : σ 0 = 1 := by
        apply Fin.eq_of_val_eq
        have := (σ 0).isLt
        have hz : (σ 0).val ≠ 0 := by
          intro hz
          exact h0 (Fin.eq_of_val_eq hz)
        omega
      have hs1 : σ 1 = 0 := by
        apply Fin.eq_of_val_eq
        have hne : σ 1 ≠ 1 := by
          intro h
          exact Fin.zero_ne_one (σ.injective (hs0.trans h.symm))
        have := (σ 1).isLt
        omega
      simpa using hs1

theorem univ_perm_fin_two :
    (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by
  ext σ
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact perm_fin_two_eq_id_or_swap σ

theorem Ioi_one_fin_two : Finset.Ioi (1 : Fin 2) = ∅ := by
  ext i
  fin_cases i <;> simp

theorem sixVertexBetheAmplitude_two_id (c : Real) (p : Fin 2 → Real) :
    sixVertexBetheAmplitude c p 1 =
      sixVertexBethePairFactor c (sixVertexBethePhase (p 0))
        (sixVertexBethePhase (p 1)) := by
  rw [sixVertexBetheAmplitude]
  simp only [Equiv.Perm.sign_one]
  norm_num
  unfold sixVertexBethePairProduct
  rw [Fin.prod_univ_two, Ioi_one_fin_two]
  simp

theorem sixVertexBetheAmplitude_two_swap (c : Real) (p : Fin 2 → Real) :
    sixVertexBetheAmplitude c p (Equiv.swap 0 1) =
      -sixVertexBethePairFactor c (sixVertexBethePhase (p 1))
        (sixVertexBethePhase (p 0)) := by
  rw [sixVertexBetheAmplitude, Equiv.Perm.sign_swap (by decide)]
  norm_num
  unfold sixVertexBethePairProduct
  rw [Fin.prod_univ_two, Ioi_one_fin_two]
  simp

theorem sixVertexBetheMonomial_two_packed_id (p : Fin 2 → Real) :
    sixVertexBetheMonomial (N := 4) p 1
        (sixVertexPackedSector 4 2 (by omega)) =
      sixVertexBethePhase (p 1) := by
  unfold sixVertexBetheMonomial
  rw [Fin.prod_univ_two, sixVertexSectorPosition_packed]
  simp [OrderEmbedding.coe_ofStrictMono]

theorem sixVertexBetheMonomial_two_packed_swap (p : Fin 2 → Real) :
    sixVertexBetheMonomial (N := 4) p (Equiv.swap 0 1)
        (sixVertexPackedSector 4 2 (by omega)) =
      sixVertexBethePhase (p 0) := by
  unfold sixVertexBetheMonomial
  rw [Fin.prod_univ_two, sixVertexSectorPosition_packed]
  simp [OrderEmbedding.coe_ofStrictMono]


theorem sixVertexCoordinateBetheWave_two_packed_eq_phase_sub
    {c : Real} {p : Fin 2 → Real} (hsymm : ∀ j, p j.rev = -p j) :
    sixVertexCoordinateBetheWave (N := 4) c p
        (sixVertexPackedSector 4 2 (by omega)) =
      2 * (sixVertexBethePhase (p 1) - sixVertexBethePhase (p 0)) := by
  have hp10 : p 1 = -p 0 := by
    simpa using hsymm (0 : Fin 2)
  let z : Complex := sixVertexBethePhase (p 0)
  have hz1 : sixVertexBethePhase (p 1) = star z := by
    rw [hp10, sixVertexBethePhase_neg]
  have hnorm : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, sixVertexBethePhase_norm]
    norm_num
  have hmul : z * star z = 1 := by
    simpa [Complex.mul_conj] using hnorm
  have hmul' : star z * z = 1 := by rw [mul_comm, hmul]
  have hswap : (Equiv.swap (0 : Fin 2) 1) ≠ 1 := by decide
  rw [sixVertexCoordinateBetheWave, univ_perm_fin_two]
  rw [Finset.sum_insert (by simpa using hswap.symm), Finset.sum_singleton]
  rw [sixVertexBetheAmplitude_two_id,
    sixVertexBetheAmplitude_two_swap,
    sixVertexBetheMonomial_two_packed_id,
    sixVertexBetheMonomial_two_packed_swap, hz1]
  change sixVertexBethePairFactor c z (star z) * star z +
      -sixVertexBethePairFactor c (star z) z * z = 2 * (star z - z)
  simp only [sixVertexBethePairFactor]
  rw [hmul, hmul']
  ring


theorem sixVertexCoordinateBetheWave_two_packed_re_eq_zero
    {c : Real} {p : Fin 2 → Real} (hsymm : ∀ j, p j.rev = -p j) :
    (sixVertexCoordinateBetheWave (N := 4) c p
      (sixVertexPackedSector 4 2 (by omega))).re = 0 := by
  have hp10 : p 1 = -p 0 := by
    simpa using hsymm (0 : Fin 2)
  let z : Complex := sixVertexBethePhase (p 0)
  have hz1 : sixVertexBethePhase (p 1) = star z := by
    rw [hp10, sixVertexBethePhase_neg]
  have hswap : (Equiv.swap (0 : Fin 2) 1) ≠ 1 := by decide
  have hconj :
      star (sixVertexBethePairFactor c z (star z) * star z) =
        sixVertexBethePairFactor c (star z) z * z := by
    simp [sixVertexBethePairFactor]
  rw [sixVertexCoordinateBetheWave, univ_perm_fin_two]
  rw [Finset.sum_insert (by simpa using hswap.symm), Finset.sum_singleton]
  rw [sixVertexBetheAmplitude_two_id,
    sixVertexBetheAmplitude_two_swap,
    sixVertexBetheMonomial_two_packed_id,
    sixVertexBetheMonomial_two_packed_swap, hz1]
  change (sixVertexBethePairFactor c z (star z) * star z +
    -sixVertexBethePairFactor c (star z) z * z).re = 0
  rw [neg_mul, ← hconj]
  simp


theorem sixVertexHalfFilledBetheRealWave_zero_at_width_four_packed
    {c : Real} (hc : 2 < c) :
    sixVertexHalfFilledBetheRealWave hc 0
      (sixVertexPackedSector 4 2 (by omega)) = 0 := by
  unfold sixVertexHalfFilledBetheRealWave
  apply sixVertexCoordinateBetheWave_two_packed_re_eq_zero
  exact (sixVertexHalfFilledBetheRoots_mem_open hc 0).2.1


theorem not_sixVertexSelectedHalfFilledWavePositive
    {c : Real} (hc : 2 < c) :
    ¬ SixVertexSelectedHalfFilledWavePositive c := by
  intro h
  have hpos := h hc 0 (sixVertexPackedSector 4 2 (by omega))
  rw [sixVertexHalfFilledBetheRealWave_zero_at_width_four_packed hc] at hpos
  exact (lt_irrefl 0) hpos


theorem sixVertexPositiveHalfBetheRoots_quantile_lower
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    Real.pi * (2 * (j : Real) + 1) <
      (sixVertexFourWidth 0 k : Real) *
        sixVertexPositiveHalfBetheRoots hc k j := by
  let i : Fin ((k + 1) + (k + 1)) := Fin.natAdd (k + 1) j
  have hopen := sixVertexHalfFilledBetheRoots_mem_open hc k
  have hrevlt : i.rev < i := by
    rw [Fin.lt_def]
    dsimp [i]
    omega
  have hspace := sixVertexBetheSolution_quantumSpacing hc hopen
    (sixVertexHalfFilledBetheRoots_is_solution hc k) hrevlt
  have hsymm := hopen.2.1 i
  have hI : sixVertexCentralQuantumNumber i -
      sixVertexCentralQuantumNumber i.rev = 2 * (j : Real) + 1 := by
    rw [sixVertexCentralQuantumNumber_eq,
      sixVertexCentralQuantumNumber_eq]
    simp only [Fin.rev, Fin.val_mk]
    dsimp [i]
    have hjle : j.val ≤ k := by omega
    have hnat : k + 1 + (k + 1) - (k + 1 + j.val + 1) =
        k - j.val := by omega
    rw [hnat]
    push_cast [Nat.cast_sub hjle]
    ring
  rw [hI, hsymm] at hspace
  change Real.pi * (2 * (j : Real) + 1) <
    (sixVertexFourWidth 0 k : Real) *
      sixVertexHalfFilledBetheRoots hc k i
  nlinarith


end
end StatMech.FrontierD
