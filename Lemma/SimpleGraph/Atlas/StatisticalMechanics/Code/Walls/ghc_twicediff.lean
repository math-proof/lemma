import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.ghc_twicediff
open Finset SimpleGraph Set StatMech StatMech.Walls


/--
[gtd_isingWeight_contDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_twicediff.lean)
-/
@[path]
private lemma gtd_isingWeight_contDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {s : ConfigSpace V} :
-- imply
  ContDiff ℝ ⊤ (fun h => isingWeight G β h s) := by
-- proof
  apply StatMech.Walls.gtd_isingWeight_contDiff G β s

/--
[gtd_num_contDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_twicediff.lean)
-/
@[path]
private lemma gtd_num_contDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {f : ConfigSpace V → ℝ} :
-- imply
  ContDiff ℝ ⊤ (fun h => ∑ s : ConfigSpace V, f s * isingWeight G β h s) := by
-- proof
  apply StatMech.Walls.gtd_num_contDiff G β f

/--
[gtd_isingZ_contDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_twicediff.lean)
-/
@[path]
private lemma gtd_isingZ_contDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ} :
-- imply
  ContDiff ℝ ⊤ (fun h => isingZ G β h) := by
-- proof
  apply StatMech.Walls.gtd_isingZ_contDiff G β

/--
[gtd_expectation_contDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_twicediff.lean)
-/
@[path]
private lemma gtd_expectation_contDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {f : ConfigSpace V → ℝ} :
-- imply
  ContDiff ℝ ⊤ (fun h => isingExpectation G β h f) := by
-- proof
  apply StatMech.Walls.gtd_expectation_contDiff G β f

/--
[gtd_magnetization_contDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_twicediff.lean)
-/
@[path]
private lemma gtd_magnetization_contDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V} :
-- imply
  ContDiff ℝ ⊤ (fun h => isingExpectation G β h (fun s => spin s o)) := by
-- proof
  apply StatMech.Walls.gtd_magnetization_contDiff G β o

/--
[gtd_magnetization_differentiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_twicediff.lean)
-/
@[path]
private lemma gtd_magnetization_differentiable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V} :
-- imply
  Differentiable ℝ (fun h => isingExpectation G β h (fun s => spin s o)) := by
-- proof
  apply StatMech.Walls.gtd_magnetization_differentiable G β o

/--
[gtd_deriv_magnetization_contDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_twicediff.lean)
-/
@[path]
private lemma gtd_deriv_magnetization_contDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V} :
-- imply
  ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv (fun h => isingExpectation G β h (fun s => spin s o))) := by
-- proof
  apply StatMech.Walls.gtd_deriv_magnetization_contDiff G β o

/--
[gtd_deriv_magnetization_differentiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_twicediff.lean)
-/
@[path]
private lemma gtd_deriv_magnetization_differentiable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V} :
-- imply
  Differentiable ℝ (deriv (fun h => isingExpectation G β h (fun s => spin s o))) := by
-- proof
  apply StatMech.Walls.gtd_deriv_magnetization_differentiable G β o

/--
[gtd_magnetization_differentiableAt_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_twicediff.lean)
-/
@[path]
private lemma gtd_magnetization_differentiableAt_deriv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V}
-- given
  (h : ℝ) :
-- imply
  DifferentiableAt ℝ (deriv (fun h => isingExpectation G β h (fun s => spin s o))) h := by
-- proof
  apply StatMech.Walls.gtd_magnetization_differentiableAt_deriv G β h o

/--
[gtd_magnetization_continuousOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_twicediff.lean)
-/
@[path]
private lemma gtd_magnetization_continuousOn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V} :
-- imply
  ContinuousOn (fun h => isingExpectation G β h (fun s => spin s o)) (Ici 0) := by
-- proof
  apply StatMech.Walls.gtd_magnetization_continuousOn G β o

/--
[gtd_magnetization_differentiableOn_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_twicediff.lean)
-/
@[path]
private lemma gtd_magnetization_differentiableOn_interior_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V} :
-- imply
  DifferentiableOn ℝ (fun h => isingExpectation G β h (fun s => spin s o)) (interior (Ici 0)) := by
-- proof
  apply StatMech.Walls.gtd_magnetization_differentiableOn_interior G β o

/--
[gtd_deriv_magnetization_differentiableOn_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_twicediff.lean)
-/
@[path]
private lemma gtd_deriv_magnetization_differentiableOn_interior_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V} :
-- imply
  DifferentiableOn ℝ (deriv (fun h => isingExpectation G β h (fun s => spin s o))) (interior (Ici 0)) := by
-- proof
  apply StatMech.Walls.gtd_deriv_magnetization_differentiableOn_interior G β o

/--
[gtd_magnetization_concaveOn_of_deriv2_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghc_twicediff.lean)
-/
@[path]
private lemma gtd_magnetization_concaveOn_of_deriv2_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V}
-- given
  (hu3 : ∀ h ∈ interior (Ici (0 : ℝ)), deriv^[2] (fun h => isingExpectation G β h (fun s => spin s o)) h ≤ 0) :
-- imply
  ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o)) := by
-- proof
  apply StatMech.Walls.gtd_magnetization_concaveOn_of_deriv2_nonpos G β o hu3


-- created on 2026-10-23
