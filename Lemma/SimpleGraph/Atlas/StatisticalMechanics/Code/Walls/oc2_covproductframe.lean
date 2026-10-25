import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc2_covproductframe.Part2
open Finset StatMech StatMech.Walls


/--
[oc2_cov_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean)
-/
@[path]
private lemma oc2_cov_frame_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {ν : E → Bool → ℝ}
  {F G : ConfigSpace E → ℝ} :
-- imply
  cov ν F G = expect ν (fun ω => F ω * G ω) - expect ν F * expect ν G := by
-- proof
  apply StatMech.Walls.oc2_cov_frame ν F G

/--
[oc2_cov_frame_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean)
-/
@[path]
private lemma oc2_cov_frame_comm_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {ν : E → Bool → ℝ}
  {F G : ConfigSpace E → ℝ} :
-- imply
  cov ν F G = cov ν G F := by
-- proof
  apply StatMech.Walls.oc2_cov_frame_comm ν F G

/--
[oc2_cov_frame_const_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean)
-/
@[path]
private lemma oc2_cov_frame_const_left_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {c : ℝ}
  {G : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  cov ν (fun _ => c) G = 0 := by
-- proof
  apply StatMech.Walls.oc2_cov_frame_const_left hν c G

/--
[oc2_cov_frame_const_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean)
-/
@[path]
private lemma oc2_cov_frame_const_right_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {c : ℝ}
  {F : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  cov ν F (fun _ => c) = 0 := by
-- proof
  apply StatMech.Walls.oc2_cov_frame_const_right hν c F

/--
[oc2_cov_coordI_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean)
-/
@[path]
private lemma oc2_cov_coordI_frame_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {ν : E → Bool → ℝ}
  {e : E}
  {f : ConfigSpace E → ℝ} :
-- imply
  cov ν (coordI e) f = expect ν (fun ω => coordI e ω * f ω) - expect ν (coordI e) * expect ν f := by
-- proof
  apply StatMech.Walls.oc2_cov_coordI_frame ν e f

/--
[oc2_expect_coordI](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean)
-/
@[path]
private lemma oc2_expect_coordI_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  expect ν (coordI e) = ν e true := by
-- proof
  apply StatMech.Walls.oc2_expect_coordI hν e

/--
[oc2_cov_coordI_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean)
-/
@[path]
private lemma oc2_cov_coordI_bernoulli_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {f : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  cov ν (coordI e) f = expect ν (fun ω => coordI e ω * f ω) - ν e true * expect ν f := by
-- proof
  apply StatMech.Walls.oc2_cov_coordI_bernoulli hν e f

/--
[oc2_cov_frame_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean)
-/
@[path]
private lemma oc2_cov_frame_add_right_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {ν : E → Bool → ℝ}
  {F G H : ConfigSpace E → ℝ} :
-- imply
  cov ν F (fun ω => G ω + H ω) = cov ν F G + cov ν F H := by
-- proof
  apply StatMech.Walls.oc2_cov_frame_add_right ν F G H

/--
[oc2_cov_frame_add_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean)
-/
@[path]
private lemma oc2_cov_frame_add_left_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {ν : E → Bool → ℝ}
  {F G H : ConfigSpace E → ℝ} :
-- imply
  cov ν (fun ω => F ω + G ω) H = cov ν F H + cov ν G H := by
-- proof
  apply StatMech.Walls.oc2_cov_frame_add_left ν F G H

/--
[oc2_cov_frame_smul_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean)
-/
@[path]
private lemma oc2_cov_frame_smul_right_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {ν : E → Bool → ℝ}
  {c : ℝ}
  {F G : ConfigSpace E → ℝ} :
-- imply
  cov ν F (fun ω => c * G ω) = c * cov ν F G := by
-- proof
  apply StatMech.Walls.oc2_cov_frame_smul_right ν c F G

/--
[oc2_cov_frame_smul_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean)
-/
@[path]
private lemma oc2_cov_frame_smul_left_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {ν : E → Bool → ℝ}
  {c : ℝ}
  {F G : ConfigSpace E → ℝ} :
-- imply
  cov ν (fun ω => c * F ω) G = c * cov ν F G := by
-- proof
  apply StatMech.Walls.oc2_cov_frame_smul_left ν c F G

/--
[oc2_var_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean)
-/
@[path]
private lemma oc2_var_frame_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {ν : E → Bool → ℝ}
  {F : ConfigSpace E → ℝ} :
-- imply
  var ν F = expect ν (fun ω => F ω * F ω) - expect ν F * expect ν F := by
-- proof
  apply StatMech.Walls.oc2_var_frame ν F

/--
[oc2_var_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean)
-/
@[path]
private lemma oc2_var_indicator_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {A : Set (ConfigSpace E)} :
-- imply
  var ν (A.indicator (fun _ => (1 : ℝ))) = expect ν (A.indicator (fun _ => (1 : ℝ))) * (1 - expect ν (A.indicator (fun _ => (1 : ℝ)))) := by
-- proof
  apply StatMech.Walls.oc2_var_indicator A

/--
[oc2_corOSSS_RHS_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean)
-/
@[path]
private lemma oc2_corOSSS_RHS_frame_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ} :
-- imply
  oc2_CovProductFrame ν f (expect ν f) (∑ e, cov ν (coordI e) f) := by
-- proof
  apply StatMech.Walls.oc2_corOSSS_RHS_frame ν f

/--
[oc2_covProductFrame_sum_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean)
-/
@[path]
private lemma oc2_covProductFrame_sum_frame_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ} :
-- imply
  (∑ e, cov ν (coordI e) f) = ∑ e, (expect ν (fun ω => coordI e ω * f ω) - expect ν (coordI e) * expect ν f) := by
-- proof
  apply StatMech.Walls.oc2_covProductFrame_sum_frame ν f

/--
[oc2_covProductFrame_sum_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean)
-/
@[path]
private lemma oc2_covProductFrame_sum_bernoulli_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  (∑ e, cov ν (coordI e) f) = ∑ e, (expect ν (fun ω => coordI e ω * f ω) - ν e true * expect ν f) := by
-- proof
  apply StatMech.Walls.oc2_covProductFrame_sum_bernoulli hν f


-- created on 2026-10-23
