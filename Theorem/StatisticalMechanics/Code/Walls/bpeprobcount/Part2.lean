/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpeprobcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bkwburtonkeane
import Theorem.StatisticalMechanics.Code.Walls.bfcforestacyclic
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Def.StatisticalMechanics.Code.Walls.bpeprobcount
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bpe_coarseTcount_le_leafCard (ω : ConfigSpace (Sym2 (Site d))) (L R m : ℕ)
    (h : bpe_CoarseForestNoBnd ω L R m) :
    bc61_coarseTcount ω L R ≤ m := by
  classical
  obtain ⟨W, _, _, _, G, _, ιT, hacyc, hmin, hdeg3, hιinj, hleaf⟩ := h
  set Tf := bc61_coarseTrifFinset ω L R with hTf
  set Tw : Finset W := Tf.image ιT with hTw
  have hιinjOn : Set.InjOn ιT Tf := by
    intro y hy z hz hyz
    rw [Finset.mem_coe, bc61_mem_coarseTrifFinset] at hy hz
    exact hιinj y hy.1 hy.2 z hz.1 hz.2 hyz
  have hcardTw : Tw.card = Tf.card := by
    rw [hTw, Finset.card_image_of_injOn hιinjOn]
  have hTwdeg : ∀ w ∈ Tw, 3 ≤ G.degree w := by
    intro w hw
    rw [hTw, Finset.mem_image] at hw
    obtain ⟨y, hyT, rfl⟩ := hw
    rw [bc61_mem_coarseTrifFinset] at hyT
    exact hdeg3 y hyT.1 hyT.2
  calc bc61_coarseTcount ω L R = Tf.card := rfl
    _ = Tw.card := hcardTw.symm
    _ ≤ (univ.filter (fun v => 3 ≤ G.degree v)).card := flc2_trifImage_card_le_deg3 G Tw hTwdeg
    _ ≤ (univ.filter (fun v => G.degree v = 1)).card :=
        flc2_forest_internal_le_leaves G hacyc hmin
    _ ≤ m := hleaf


theorem bpe_noBnd_of_fullForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc61_CoarseForestLeafCount ω L R) :
    bpe_CoarseForestNoBnd ω L R (boxSV_boundaryCard d R) := by
  classical
  obtain ⟨W, hWf, hWne, hWde, G, hGdr, ιT, lamL, hacyc, hmin, hdeg3, hιinj, hlammap, hlaminj⟩ := h
  refine ⟨W, hWf, hWne, hWde, G, hGdr, ιT, hacyc, hmin, hdeg3, hιinj, ?_⟩
  exact flc2_leaf_card_le_boundary G R lamL hlammap hlaminj


theorem bpe_expBound_of_perConfigLeaf
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) (L : ℕ) (bdry : ℕ → ℕ)
    (leafBd : ConfigSpace (Sym2 (Site d)) → ℕ → ℕ)
    (hle : ∀ ω R, bc61_coarseTcount ω L R ≤ leafBd ω R)
    (hExp : ∀ R, ∫⁻ ω, (leafBd ω R : ENNReal) ∂μ ≤ (bdry R : ENNReal)) :
    ∀ R : ℕ, ∫⁻ ω, (bc61_coarseTcount ω L R : ENNReal) ∂μ ≤ (bdry R : ENNReal) := by
  intro R
  refine le_trans (lintegral_mono (fun ω => ?_)) (hExp R)
  exact Nat.cast_le.mpr (hle ω R)


theorem bpe_top_null_of_probForest
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (hd : 1 ≤ d) (L : ℕ)
    (bdry : ℕ → ℕ) (leafBd : ConfigSpace (Sym2 (Site d)) → ℕ → ℕ)
    (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ),
      bpe_CoarseForestNoBnd ω L R (leafBd ω R))
    (hExpLeaf : ∀ R, ∫⁻ ω, (leafBd ω R : ENNReal) ∂μ ≤ (bdry R : ENNReal))
    (hdens : Filter.Tendsto
      (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0))
    (hexist : bc61_CoarseTrifExistence μ L) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
  
  have ha : ∀ ω R, bc61_coarseTcount ω L R ≤ leafBd ω R :=
    fun ω R => bpe_coarseTcount_le_leafCard ω L R (leafBd ω R) (hforest ω R)
  
  have hExpBound : ∀ R : ℕ, ∫⁻ ω, (bc61_coarseTcount ω L R : ENNReal) ∂μ ≤ (bdry R : ENNReal) :=
    bpe_expBound_of_perConfigLeaf μ L bdry leafBd ha hExpLeaf
  
  exact bpe_top_null_of_expCount μ L bdry
    (fun R => bc62_coarse_expectation μ hinv L R) hExpBound
    (fun R => bkc_boxFinsetBK_card_pos d R) hdens hexist


theorem bpe_status (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (hd : 1 ≤ d) (L : ℕ)
    (bdry : ℕ → ℕ) :
    
    ((∀ R : ℕ,
        ((boxFinsetBK d R).card : ENNReal) * μ {ω | bc61_IsCoarseTrifurcation ω L 0}
          = ∫⁻ ω, (bc61_coarseTcount ω L R : ENNReal) ∂μ) →
      (∀ R : ℕ, ∫⁻ ω, (bc61_coarseTcount ω L R : ENNReal) ∂μ ≤ (bdry R : ENNReal)) →
      (∀ R, 0 < (boxFinsetBK d R).card) →
      Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0) →
      bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (R m : ℕ),
      bpe_CoarseForestNoBnd ω L R m → bc61_coarseTcount ω L R ≤ m) ∧
    
    (∀ (leafBd : ConfigSpace (Sym2 (Site d)) → ℕ → ℕ),
      (∀ ω R, bpe_CoarseForestNoBnd ω L R (leafBd ω R)) →
      (∀ R, ∫⁻ ω, (leafBd ω R : ENNReal) ∂μ ≤ (bdry R : ENNReal)) →
      Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0) →
      bc61_CoarseTrifExistence μ L →
      μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hexp hExpBound hvol hdens hexist
    exact bpe_top_null_of_expCount μ L bdry hexp hExpBound hvol hdens hexist
  · intro ω R m h; exact bpe_coarseTcount_le_leafCard ω L R m h
  · intro leafBd hforest hExpLeaf hdens hexist
    exact bpe_top_null_of_probForest μ hinv hd L bdry leafBd hforest hExpLeaf hdens hexist

end StatMech.Walls
