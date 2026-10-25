import Mathlib
import Def.TateCurve_XMultIdentities
import Def.TateCurve_KeystoneVocab

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Filter
open WeierstrassCurve.Affine

set_option linter.unusedSectionVars false

open WeierstrassCurve.Affine


set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Region

variable {q u v : K}

structure ExpansionRegion (q u v : K) : Prop where
  params : AddParams q u v
  norm_q_lt_one : ‖q‖ < 1
  u_lo : ‖q‖ < ‖u‖
  u_hi : ‖q‖ * ‖u‖ < 1
  v_lo : ‖q‖ < ‖v‖
  v_hi : ‖q‖ * ‖v‖ < 1
  mul_lo : ‖q‖ < ‖u * v‖
  mul_hi : ‖q‖ * ‖u * v‖ < 1
  div_lo : ‖q‖ < ‖u * v⁻¹‖
  div_hi : ‖q‖ * ‖u * v⁻¹‖ < 1

end Region

end TateCurve
