import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds
open scoped Manifold
open DifferentialFormSpace


/--
[DifferentialFormSpace.ι_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/KahlerManifolds.lean)
-/
@[path]
lemma DifferentialFormSpace.ι_sub
  {Ω : ℕ → Type*} [inst : DifferentialFormSpace Ω VF]
  {X : VF}
  {p : ℕ}
  {a b : Ω (p + 1)} :
-- imply
  inst.ι X (a - b) = inst.ι X a - inst.ι X b := by
-- proof
  have h1 : a - b = a + (-1 : ℝ) • b := by rw [neg_one_smul]; abel
  rw [h1, inst.ι_add X a ((-1 : ℝ) • b), inst.ι_smul X (-1 : ℝ) b]
  rw [neg_one_smul, sub_eq_add_neg]

/--
[DifferentialFormSpace.d_neg_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/KahlerManifolds.lean)
-/
@[path]
lemma DifferentialFormSpace.d_neg_zero
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {f : Ω 0} :
-- imply
  inst.d (-f) = -(inst.d f) := by
-- proof
  have h1 : -f = (-1 : ℝ) • f := by rw [neg_one_smul]
  rw [h1, inst.d_smul (-1) f, neg_one_smul]

/--
[DifferentialFormSpace.ι_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/KahlerManifolds.lean)
-/
@[path]
lemma DifferentialFormSpace.ι_neg
  {Ω : ℕ → Type*} [inst : DifferentialFormSpace Ω VF]
  {X : VF}
  {p : ℕ}
  {g : Ω (p + 1)} :
-- imply
  inst.ι X (-g) = -(inst.ι X g) := by
-- proof
  have h1 : -g = (-1 : ℝ) • g := by rw [neg_one_smul]
  rw [h1, inst.ι_smul X (-1 : ℝ) g, neg_one_smul]

/--
[nijenhuis_dual_eq_dForm_20_re_raw](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/KahlerManifolds.lean)
-/
@[path]
lemma nijenhuis_dual_eq_dForm_20_re_raw
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hbr : HasLieBracket Ω VF]
  {nij : NijenhuisTensor J}
  {α β : Ω 1}
  {u v : VF}
-- given
  (J : AlmostComplexStr (inst := inst))
  (h : IsNijenhuisOf J nij)
  (htype : ∀ (X : VF), inst.ι X β = inst.ι (J.J X) α) :
-- imply
  inst.ι v (inst.ι u (inst.d α)) - inst.ι (J.J v) (inst.ι (J.J u) (inst.d α)) + inst.ι (J.J v) (inst.ι u (inst.d β)) + inst.ι v (inst.ι (J.J u) (inst.d β)) = inst.ι (nij.N u v) α := by
-- proof
  have key : ∀ (X Y : VF) (ω : Ω 1),
    inst.ι Y (inst.ι X (inst.d ω)) =
      inst.ι X (inst.d (inst.ι Y ω)) - inst.ι Y (inst.d (inst.ι X ω))
      - inst.ι (hbr.bracket X Y) ω := by
    intro X Y ω
    have hcartan : inst.ι X (inst.d ω) = inst.L X ω - inst.d (inst.ι X ω) := by
      have hc := cartan_formula X ω; rw [hc]; abel
    rw [hcartan, DifferentialFormSpace.ι_sub]
    have hbracket : inst.ι Y (inst.L X ω) =
      inst.L X (inst.ι Y ω) - inst.ι (hbr.bracket X Y) ω := by
      have hb := hbr.bracket_ι_eq X Y ω; rw [hb]; abel
    rw [hbracket, inst.L_zero_eq_ι_d X (inst.ι Y ω)]
    abel
  rw [key u v α, key (J.J u) (J.J v) α, key u (J.J v) β, key (J.J u) v β]
  simp only [htype]
  simp only [J.sq_neg_id]
  simp only [DifferentialFormSpace.d_neg_zero, DifferentialFormSpace.ι_neg]
  rw [h.nijenhuis_eq u v α]
  abel

/--
[nijenhuis_dual_eq_dForm_20_proj_re](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/KahlerManifolds.lean)
-/
@[path]
lemma nijenhuis_dual_eq_dForm_20_proj_re
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hbr : HasLieBracket Ω VF]
  {nij : NijenhuisTensor J}
  {f : Form01 J}
  {u v : VF}
-- given
  (J : AlmostComplexStr (inst := inst))
  (h : IsNijenhuisOf J nij) :
-- imply
  dForm_20_proj J f u v = nijenhuis_dual_eval nij f u v :=
-- proof
  nijenhuis_dual_eq_dForm_20_re_raw J nij h f.re f.im f.type_cond u v

/--
[nijenhuis_dual_eq_dForm_20_im_raw](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/KahlerManifolds.lean)
-/
@[path]
lemma nijenhuis_dual_eq_dForm_20_im_raw
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hbr : HasLieBracket Ω VF]
  {nij : NijenhuisTensor J}
  {α β : Ω 1}
  {u v : VF}
-- given
  (J : AlmostComplexStr (inst := inst))
  (h : IsNijenhuisOf J nij)
  (htype : ∀ (X : VF), inst.ι X β = inst.ι (J.J X) α) :
-- imply
  inst.ι v (inst.ι u (inst.d β)) - inst.ι (J.J v) (inst.ι (J.J u) (inst.d β)) - inst.ι v (inst.ι (J.J u) (inst.d α)) - inst.ι (J.J v) (inst.ι u (inst.d α)) = inst.ι (J.J (nij.N u v)) α := by
-- proof
  have key : ∀ (X Y : VF) (ω : Ω 1),
    inst.ι Y (inst.ι X (inst.d ω)) =
      inst.ι X (inst.d (inst.ι Y ω)) - inst.ι Y (inst.d (inst.ι X ω))
      - inst.ι (hbr.bracket X Y) ω := by
    intro X Y ω
    have hcartan : inst.ι X (inst.d ω) = inst.L X ω - inst.d (inst.ι X ω) := by
      have hc := cartan_formula X ω; rw [hc]; abel
    rw [hcartan, DifferentialFormSpace.ι_sub]
    have hbracket : inst.ι Y (inst.L X ω) =
      inst.L X (inst.ι Y ω) - inst.ι (hbr.bracket X Y) ω := by
      have hb := hbr.bracket_ι_eq X Y ω; rw [hb]; abel
    rw [hbracket, inst.L_zero_eq_ι_d X (inst.ι Y ω)]
    abel
  rw [key u v β, key (J.J u) (J.J v) β, key (J.J u) v α, key u (J.J v) α]
  simp only [htype]
  simp only [J.sq_neg_id]
  simp only [DifferentialFormSpace.d_neg_zero, DifferentialFormSpace.ι_neg]
  rw [h.nijenhuis_eq_J u v α]
  simp only [J.sq_neg_id]
  abel

/--
[nijenhuis_dual_eq_dForm_20_proj_im](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/KahlerManifolds.lean)
-/
@[path]
lemma nijenhuis_dual_eq_dForm_20_proj_im
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hbr : HasLieBracket Ω VF]
  {nij : NijenhuisTensor J}
  {f : Form01 J}
  {u v : VF}
-- given
  (J : AlmostComplexStr (inst := inst))
  (h : IsNijenhuisOf J nij) :
-- imply
  dForm_20_proj_im J f u v = nijenhuis_dual_eval_im nij f u v := by
-- proof
  unfold dForm_20_proj_im nijenhuis_dual_eval_im
  rw [f.type_cond (nij.N u v)]
  exact nijenhuis_dual_eq_dForm_20_im_raw J nij h f.re f.im f.type_cond u v

/--
[nijenhuis_dual_map_is_d_20_typed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/KahlerManifolds.lean)
-/
@[path]
lemma nijenhuis_dual_map_is_d_20_typed
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [HasLieBracket Ω VF]
  {nij : NijenhuisTensor J}
  {f : Form01 J}
  {u v : VF}
-- given
  (J : AlmostComplexStr (inst := inst))
  (h : IsNijenhuisOf J nij) :
-- imply
  dForm_20_proj J f u v = nijenhuis_dual_eval nij f u v :=
-- proof
  nijenhuis_dual_eq_dForm_20_proj_re J nij h f u v


-- created on 2026-10-23
