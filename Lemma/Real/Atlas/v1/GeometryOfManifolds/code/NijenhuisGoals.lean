import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.NijenhuisGoals.Part2
open DifferentialFormSpace MfdNijenhuis
open scoped Manifold


/--
[nijenhuis_expr_vanishes_on_pullback](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/NijenhuisGoals.lean)
-/
@[path]
lemma nijenhuis_expr_vanishes_on_pullback
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hbr : HasLieBracket Ω VF]
  {Ω_loc : ℕ → Type}
  {VF_loc : Type}
  {inst_loc : DifferentialFormSpace Ω_loc VF_loc}
  {φ : @DFSMorphism Ω VF Ω_loc VF_loc inst inst_loc}
  {J_loc_star : Ω_loc 1 → Ω_loc 1}
  {X Y : VF}
  {α_loc : Ω_loc 1}
-- given
  (J : AlmostComplexStr (inst := inst))
  (h_holo : ∀ (X : VF) (α : Ω_loc 1), inst.ι (J.J X) (φ.pullback α) = inst.ι X (φ.pullback (J_loc_star α)))
  (h_flat : ∀ (X Y : VF) (α_loc : Ω_loc 1), inst.ι (hbr.bracket X Y) (φ.pullback α_loc) = 0) :
-- imply
  inst.ι (hbr.bracket (J.J X) (J.J Y)) (φ.pullback α_loc) - inst.ι (J.J (hbr.bracket (J.J X) Y)) (φ.pullback α_loc) - inst.ι (J.J (hbr.bracket X (J.J Y))) (φ.pullback α_loc) - inst.ι (hbr.bracket X Y) (φ.pullback α_loc) = 0 := by
-- proof
  have h1 : inst.ι (hbr.bracket (J.J X) (J.J Y)) (φ.pullback α_loc) = 0 :=
    h_flat (J.J X) (J.J Y) α_loc
  have h2 : inst.ι (J.J (hbr.bracket (J.J X) Y)) (φ.pullback α_loc) = 0 := by
    rw [h_holo (hbr.bracket (J.J X) Y) α_loc]
    exact h_flat (J.J X) Y (J_loc_star α_loc)
  have h3 : inst.ι (J.J (hbr.bracket X (J.J Y))) (φ.pullback α_loc) = 0 := by
    rw [h_holo (hbr.bracket X (J.J Y)) α_loc]
    exact h_flat X (J.J Y) (J_loc_star α_loc)
  have h4 : inst.ι (hbr.bracket X Y) (φ.pullback α_loc) = 0 :=
    h_flat X Y α_loc
  rw [h1, h2, h3, h4]
  simp

/--
[isIntegrable_of_hasHolomorphicCoords](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/NijenhuisGoals.lean)
-/
@[path]
lemma isIntegrable_of_hasHolomorphicCoords
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [HasLieBracket Ω VF]
  {nij : NijenhuisTensor J}
-- given
  (J : AlmostComplexStr (inst := inst))
  (h_nij : IsNijenhuisOf J nij)
  (hJ : HasHolomorphicCoords J) :
-- imply
  IsIntegrable J nij := by
-- proof
  constructor
  intro u v β
  obtain ⟨Ω_loc, VF_loc, inst_loc, _J_loc, φ, J_loc_star,
    h_holo, _h_sq, h_flat, h_nondeg⟩ := hJ.holo_coords
  have h_pullback_zero : ∀ (α_loc : Ω_loc 1),
    inst.ι (nij.N u v) (φ.pullback α_loc) = 0 := by
    intro α_loc
    rw [h_nij.nijenhuis_eq u v (φ.pullback α_loc)]
    exact nijenhuis_expr_vanishes_on_pullback J φ J_loc_star h_holo h_flat u v α_loc
  exact h_nondeg (nij.N u v) h_pullback_zero β
section MfdGoal39
namespace MfdNijenhuis
open scoped Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace MfdNijenhuis

/--
[nijenhuis_dual_map_is_d_20_typed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/NijenhuisGoals.lean)
-/
@[path]
lemma nijenhuis_dual_map_is_d_20_typed
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M]
  [ChartedSpace H M]
  {Jstr : ACSOnMfd I M}
  {ops : CartanDataOnMfd I M Jstr}
  {f : Form01OnMfd Jstr}
  {x : M}
-- given
  (U V : ∀ x : M, TangentSpace I x) :
-- imply
  (ops.dForm20 f x) ![U x, V x] = nijDualEvalOnMfd Jstr f U V x := by
-- proof
  rw [ops.dForm20_eval]
  unfold nijDualEvalOnMfd
  set JU := fun y => Jstr.J y (U y)
  set JV := fun y => Jstr.J y (V y)
  rw [ops.cartan f.re U V x, ops.cartan f.re JU JV x,
    ops.cartan f.im U JV x, ops.cartan f.im JU V x]
  have tc1 : ∀ y, (f.im y) (JV y) = -(f.re y) (V y) := by
    intro y; rw [f.type_cond JV y, Jstr.sq_neg, map_neg]
  have tc2 : ∀ y, (f.im y) (U y) = (f.re y) (Jstr.J y (U y)) :=
    fun y => f.type_cond U y
  have tc3 : ∀ y, (f.im y) (V y) = (f.re y) (Jstr.J y (V y)) :=
    fun y => f.type_cond V y
  have tc4 : ∀ y, (f.im y) (JU y) = -(f.re y) (U y) := by
    intro y; rw [f.type_cond JU y, Jstr.sq_neg, map_neg]
  have h_im_JV : (fun y => (f.im y) (JV y)) = (fun y => -(f.re y) (V y)) := funext tc1
  have h_im_U : (fun y => (f.im y) (U y)) = (fun y => (f.re y) (Jstr.J y (U y))) := funext tc2
  have h_im_V : (fun y => (f.im y) (V y)) = (fun y => (f.re y) (Jstr.J y (V y))) := funext tc3
  have h_im_JU : (fun y => (f.im y) (JU y)) = (fun y => -(f.re y) (U y)) := funext tc4
  have h_re_JV : (fun y => (f.re y) (JV y)) = (fun y => (f.re y) (Jstr.J y (V y))) := rfl
  have h_re_JU : (fun y => (f.re y) (JU y)) = (fun y => (f.re y) (Jstr.J y (U y))) := rfl
  rw [h_im_JV, h_im_U, h_im_V, h_im_JU, h_re_JV, h_re_JU]
  simp only [ops.lieD_neg]
  have tc_br1 : (f.im x) (VectorField.mlieBracket I U JV x) =
    (f.re x) (Jstr.J x (VectorField.mlieBracket I U JV x)) :=
    f.type_cond (fun z => VectorField.mlieBracket I U JV z) x
  have tc_br2 : (f.im x) (VectorField.mlieBracket I JU V x) =
    (f.re x) (Jstr.J x (VectorField.mlieBracket I JU V x)) :=
    f.type_cond (fun z => VectorField.mlieBracket I JU V z) x
  rw [tc_br1, tc_br2]
  unfold nijenhuisTensorMfd
  simp only [map_sub]
  ring
end MfdNijenhuis
end MfdGoal39



-- created on 2026-10-23
