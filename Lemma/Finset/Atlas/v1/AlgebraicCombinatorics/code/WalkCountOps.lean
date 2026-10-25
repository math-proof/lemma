import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicCombinatorics.code.WalkCountOps
open WalkCountFormula
open scoped Classical


namespace WalkCountFormula

/--
[liftU_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma liftU_single
  {lam : YoungDiagram}
  {c : ℤ} :
-- imply
  liftU (Finsupp.single lam c) = c • YoungDiagram.raisingOp lam := by
-- proof
  simp only [liftU, Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_apply]

end WalkCountFormula

namespace WalkCountFormula

/--
[liftD_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma liftD_single
  {lam : YoungDiagram}
  {c : ℤ} :
-- imply
  liftD (Finsupp.single lam c) = c • YoungDiagram.loweringOp lam := by
-- proof
  simp only [liftD, Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_apply]

end WalkCountFormula

namespace WalkCountFormula

/--
[liftU_single_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma liftU_single_one
  {lam : YoungDiagram} :
-- imply
  liftU (Finsupp.single lam 1) = YoungDiagram.raisingOp lam := by
-- proof
  simp

end WalkCountFormula

namespace WalkCountFormula

/--
[liftD_single_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma liftD_single_one
  {lam : YoungDiagram} :
-- imply
  liftD (Finsupp.single lam 1) = YoungDiagram.loweringOp lam := by
-- proof
  simp

end WalkCountFormula

namespace WalkCountFormula

/--
[bot_colLen_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma bot_colLen_zero
-- imply
  (⊥ : YoungDiagram).colLen 0 = 0 := by
-- proof
  by_contra h
  have hpos : 0 < (⊥ : YoungDiagram).colLen 0 := Nat.pos_of_ne_zero h
  have hmem : (0, 0) ∈ (⊥ : YoungDiagram) := YoungDiagram.mem_iff_lt_colLen.mpr hpos
  have : (0, 0) ∈ (⊥ : YoungDiagram).cells := hmem
  simp at this

end WalkCountFormula

namespace WalkCountFormula

/--
[removableRows_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma removableRows_bot
-- imply
  YoungDiagram.removableRows ⊥ = ∅ := by
-- proof
  simp only [YoungDiagram.removableRows, bot_colLen_zero, Finset.range_zero, Finset.filter_empty]

end WalkCountFormula

namespace WalkCountFormula

/--
[coversDown_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma coversDown_bot
-- imply
  YoungDiagram.coversDown ⊥ = ∅ := by
-- proof
  simp only [YoungDiagram.coversDown, removableRows_bot, Finset.image_empty]

end WalkCountFormula

namespace WalkCountFormula

/--
[loweringOp_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma loweringOp_bot
-- imply
  YoungDiagram.loweringOp ⊥ = 0 := by
-- proof
  simp only [YoungDiagram.loweringOp, coversDown_bot, Finset.sum_empty]

end WalkCountFormula

namespace WalkCountFormula

/--
[liftD_emptyBasis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma liftD_emptyBasis
-- imply
  liftD emptyBasis = 0 := by
-- proof
  simp only [emptyBasis, liftD_single, one_smul, loweringOp_bot]

end WalkCountFormula

namespace WalkCountFormula

/--
[iterU_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma iterU_zero
-- imply
  iterU 0 = LinearMap.id := by
-- proof
  show liftU ^ 0 = LinearMap.id
  rw [pow_zero]
  rfl

end WalkCountFormula

namespace WalkCountFormula

/--
[iterU_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma iterU_succ
  {n : ℕ} :
-- imply
  iterU (n + 1) = iterU n ∘ₗ liftU := by
-- proof
  show liftU ^ (n + 1) = (liftU ^ n) ∘ₗ liftU
  rw [pow_succ, Module.End.mul_eq_comp]

end WalkCountFormula

namespace WalkCountFormula

/--
[raisingOp_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma raisingOp_apply
  {ν mu : YoungDiagram} :
-- imply
  (YoungDiagram.raisingOp ν) mu = if mu ∈ ν.coversUp then 1 else 0 := by
-- proof
  simp only [YoungDiagram.raisingOp]
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply]
  simp [Finset.sum_ite_eq']

end WalkCountFormula

namespace WalkCountFormula

/--
[loweringOp_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma loweringOp_apply
  {σ mu : YoungDiagram} :
-- imply
  (YoungDiagram.loweringOp σ) mu = if mu ∈ σ.coversDown then 1 else 0 := by
-- proof
  simp only [YoungDiagram.loweringOp]
  rw [Finset.sum_apply']
  simp only [Finsupp.single_apply]
  simp [Finset.sum_ite_eq']

end WalkCountFormula

namespace WalkCountFormula

/--
[liftD_raisingOp_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma liftD_raisingOp_apply
  {lam mu : YoungDiagram} :
-- imply
  (liftD (YoungDiagram.raisingOp lam)) mu = YoungDiagram.DU_apply lam mu := by
-- proof
  simp only [YoungDiagram.raisingOp, YoungDiagram.DU_apply, map_sum, liftD_single, one_smul]
  rw [Finset.sum_apply']

end WalkCountFormula

namespace WalkCountFormula

/--
[liftU_loweringOp_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma liftU_loweringOp_apply
  {lam mu : YoungDiagram} :
-- imply
  (liftU (YoungDiagram.loweringOp lam)) mu = YoungDiagram.UD_apply lam mu := by
-- proof
  simp only [YoungDiagram.loweringOp, YoungDiagram.UD_apply, map_sum, liftU_single, one_smul]
  rw [Finset.sum_apply']

end WalkCountFormula

namespace WalkCountFormula

/--
[DU_apply_eq_DUCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma DU_apply_eq_DUCoeff
  {lam mu : YoungDiagram} :
-- imply
  YoungDiagram.DU_apply lam mu = ↑(YoungDiagram.DUCoeff lam mu) := by
-- proof
  simp only [YoungDiagram.DU_apply, YoungDiagram.DUCoeff]
  simp_rw [loweringOp_apply]
  rw [Finset.sum_boole]

end WalkCountFormula

namespace WalkCountFormula

/--
[UD_apply_eq_UDCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma UD_apply_eq_UDCoeff
  {lam mu : YoungDiagram} :
-- imply
  YoungDiagram.UD_apply lam mu = ↑(YoungDiagram.UDCoeff lam mu) := by
-- proof
  simp only [YoungDiagram.UD_apply, YoungDiagram.UDCoeff]
  simp_rw [raisingOp_apply]
  rw [Finset.sum_boole]

end WalkCountFormula

namespace WalkCountFormula

/--
[liftD_comp_liftU_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma liftD_comp_liftU_sub
  {f : YoungDiagram →₀ ℤ} :
-- imply
  liftD (liftU f) - liftU (liftD f) = f := by
-- proof
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add]
    rw [add_sub_add_comm, hf, hg]
  | single a c =>
    simp only [liftU_single, liftD_single, map_smul]
    rw [← smul_sub]
    rw [show Finsupp.single a c = c • Finsupp.single a (1 : ℤ) from by
      rw [Finsupp.smul_single', mul_one]]
    congr 1
    ext mu
    simp only [Finsupp.sub_apply, Finsupp.single_apply]
    rw [liftD_raisingOp_apply, liftU_loweringOp_apply,
      DU_apply_eq_DUCoeff, UD_apply_eq_UDCoeff]
    have h := YoungDiagram.young_commutation_coeff a mu
    split_ifs with heq
    · subst heq; simp only [ite_true] at h; linarith
    · rw [if_neg heq] at h; linarith

end WalkCountFormula

namespace WalkCountFormula

/--
[iterU_succ'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma iterU_succ'
  {n : ℕ} :
-- imply
  iterU (n + 1) = liftU ∘ₗ iterU n := by
-- proof
  show liftU ^ (n + 1) = liftU ∘ₗ (liftU ^ n)
  rw [pow_succ', Module.End.mul_eq_comp]

end WalkCountFormula

namespace WalkCountFormula

/--
[liftD_liftU_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma liftD_liftU_eq
  {f : YoungDiagram →₀ ℤ} :
-- imply
  liftD (liftU f) = liftU (liftD f) + f := by
-- proof
  have h := liftD_comp_liftU_sub f
  rw [sub_eq_iff_eq_add] at h
  rwa [add_comm] at h

end WalkCountFormula

namespace WalkCountFormula

/--
[liftD_iterU_emptyBasis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean)
-/
@[path]
lemma liftD_iterU_emptyBasis
  {k : ℕ} :
-- imply
  liftD (iterU k emptyBasis) = (k : ℤ) • iterU (k - 1) emptyBasis := by
-- proof
  induction k with
  | zero =>
    simp only [iterU_zero, LinearMap.id_apply, liftD_emptyBasis, Nat.zero_sub,
      Nat.cast_zero, zero_smul]
  | succ n ih =>
    simp only [Nat.succ_sub_one]
    rw [iterU_succ', LinearMap.comp_apply, liftD_liftU_eq, ih, map_smul]
    cases n with
    | zero =>
      simp only [Nat.zero_sub, iterU_zero, LinearMap.id_apply, Nat.cast_zero, zero_smul,
        zero_add, Nat.cast_one, one_smul]
    | succ m =>
      simp only [Nat.succ_sub_one]
      rw [← LinearMap.comp_apply (f := liftU) (g := iterU m), ← iterU_succ']
      have : ((↑(m + 1) + 1 : ℤ)) = (↑(m + 1 + 1) : ℤ) := by push_cast; ring
      rw [← this, add_smul, one_smul]
end WalkCountFormula



-- created on 2026-10-23
