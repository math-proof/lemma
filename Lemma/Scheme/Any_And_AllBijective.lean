import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private noncomputable def res
  {X : (Scheme : Type (u + 1))} (M : X.Modules) (m : (Scheme.Modules.presheaf M).obj (op ⊤)) (W : X.Opens) :
    (Scheme.Modules.presheaf M).obj (op W) :=
  M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op m

private lemma res_map
  {X : (Scheme : Type (u + 1))} (M : X.Modules) (m : (Scheme.Modules.presheaf M).obj (op ⊤)) {W W' : X.Opens} (i : W' ⟶ W) :
    M.presheaf.map i.op (res M m W) = res M m W' := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

private lemma smul_res
  {X : (Scheme : Type (u + 1))} (M : X.Modules) (m : (Scheme.Modules.presheaf M).obj (op ⊤)) {W W' : X.Opens} (i : W' ⟶ W) (g : X.presheaf.obj (op W)) :
    M.presheaf.map i.op (g • res M m W) = X.presheaf.map i.op g • res M m W' := by
  rw [Scheme.Modules.map_smul, res_map]

private lemma helper_main
  {X : (Scheme : Type (u + 1))} (M : X.Modules) [Fintype ι] (a : ι → X.presheaf.obj (op ⊤)) (t : ι → (Scheme.Modules.presheaf M).obj (op ⊤)) (x : X)
  (h : ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U → Function.Bijective fun g : X.presheaf.obj (op V) => g • res M (∑ j, a j • t j) V) :
    ∃ (j : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U → Function.Bijective fun g : X.presheaf.obj (op V) => g • res M (t j) V := by
  classical
  obtain ⟨U, hxU, hU⟩ := h
  set s : (Scheme.Modules.presheaf M).obj (op ⊤) := ∑ j, a j • t j with hs
  have hbU := hU U le_rfl
  choose hj hhj using fun j => hbU.2 (res M (t j) U)
  have hhj' : ∀ j, hj j • res M s U = res M (t j) U := hhj
  have hsum : ∑ j, X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (a j) * hj j = 1 := by
    apply hbU.1
    show (∑ j, X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (a j) * hj j) • res M s U = (1 : X.presheaf.obj (op U)) • res M s U
    rw [one_smul, Finset.sum_smul]
    simp_rw [mul_smul, hhj']
    rw [hs]
    simp only [res, map_sum, Scheme.Modules.map_smul]
  obtain ⟨j, hju⟩ : ∃ j, IsUnit (X.presheaf.germ U x hxU (hj j)) := by
    by_contra hcon
    push Not at hcon
    have h1 : X.presheaf.germ U x hxU (∑ j, X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (a j) * hj j) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
      rw [map_sum]
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [map_mul]
      apply Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hcon j))
    rw [hsum, map_one] at h1
    apply (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  refine ⟨j, X.basicOpen (hj j), (X.mem_basicOpen (hj j) x hxU).2 hju, fun V hV => ?_⟩
  have hVU : V ≤ U := hV.trans (X.basicOpen_le _)
  have hu : IsUnit (X.presheaf.map (homOfLE hVU).op (hj j)) := by
    have h0 := RingedSpace.isUnit_res_basicOpen (X := X.toLocallyRingedSpace.toSheafedSpace) (hj j)
    have hcomp : X.presheaf.map (homOfLE hVU).op (hj j) = X.presheaf.map (homOfLE hV).op (X.presheaf.map (homOfLE (X.basicOpen_le (hj j))).op (hj j)) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl
    rw [hcomp]
    apply h0.map (CommRingCat.Hom.hom (X.presheaf.map (homOfLE hV).op))
  have htV : res M (t j) V = X.presheaf.map (homOfLE hVU).op (hj j) • res M s V := by
    rw [← smul_res M s (homOfLE hVU) (hj j), hhj', res_map]
  have hbV := hU V hVU
  have hmul : Function.Bijective fun g : X.presheaf.obj (op V) => g * X.presheaf.map (homOfLE hVU).op (hj j) := by
    obtain ⟨u', hu'⟩ := hu
    rw [← hu']
    apply (Units.mulRight u').bijective
  have key : (fun g : X.presheaf.obj (op V) => g • res M (t j) V) = (fun g : X.presheaf.obj (op V) => g • res M s V) ∘ (fun g => g * X.presheaf.map (homOfLE hVU).op (hj j)) := by
    funext g
    simp only [Function.comp_apply, htV, mul_smul]
  rw [key]
  apply hbV.comp hmul

/--
[AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_sum_smul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_sum_smul.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type (u + 1))} (M : X.Modules) [Fintype ι] (a : ι → X.presheaf.obj (op ⊤)) (t : ι → (Scheme.Modules.presheaf M).obj (op ⊤)) (x : X)
  (h : ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U → Function.Bijective fun g : X.presheaf.obj (op V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (∑ j, a j • t j) : (Scheme.Modules.presheaf M).obj (op V))) :
    ∃ (j : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U → Function.Bijective fun g : X.presheaf.obj (op V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (t j) : (Scheme.Modules.presheaf M).obj (op V)) :=
  helper_main M a t x h


-- created on 2026-10-20
