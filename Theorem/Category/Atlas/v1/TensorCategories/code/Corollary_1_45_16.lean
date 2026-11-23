module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
public import Theorem.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron

public section

open Real


/--
[corollary_1_45_16_fpdim_cosine](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_45_16.lean)
-/
@[path]
public theorem corollary_1_45_16_fpdim_cosine
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {fpd : R.FPdimData}
  {i : ι}
-- given
  (hi : fpd.d i < 2) :
-- imply
  ∃ n : ℕ, n ≥ 3 ∧ fpd.d i = 2 * Real.cos (Real.pi / (n : ℝ)) :=
-- proof
  fpd.FPdim_lt_two_eq_cos i hi


-- created on 2026-10-23
