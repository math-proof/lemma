import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private noncomputable def res
  {X : (Scheme : Type (u + 1))} (M : X.Modules)
  (σ : (Scheme.Modules.presheaf M).obj (op ⊤)) (W : X.Opens) :
    (Scheme.Modules.presheaf M).obj (op W) :=
  M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ

private lemma res_map
  {X : (Scheme : Type (u + 1))} (M : X.Modules)
  (σ : (Scheme.Modules.presheaf M).obj (op ⊤))
  {W W' : X.Opens} (i : W' ⟶ W) :
    M.presheaf.map i.op (res M σ W) = res M σ W' := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

private lemma smul_res
  {X : (Scheme : Type (u + 1))} (M : X.Modules)
  (σ : (Scheme.Modules.presheaf M).obj (op ⊤))
  {W W' : X.Opens} (i : W' ⟶ W) (g : X.presheaf.obj (op W)) :
    M.presheaf.map i.op (g • res M σ W) = X.presheaf.map i.op g • res M σ W' := by
  rw [Scheme.Modules.map_smul, res_map]

private noncomputable def abSheaf
  {X : (Scheme : Type (u + 1))} (M : X.Modules) :
    TopCat.Sheaf Ab X.carrier :=
  ⟨M.presheaf, M.isSheaf⟩

private lemma helper_main
  {X : (Scheme : Type (u + 1))} (M : X.Modules)
  (σ : (Scheme.Modules.presheaf M).obj (op ⊤)) (V : X.Opens)
  (h : ∀ x ∈ V, ∃ U : X.Opens, x ∈ U ∧ ∀ W : X.Opens, W ≤ U → Function.Bijective fun g : X.presheaf.obj (op W) => g • res M σ W) :
    Function.Bijective fun g : X.presheaf.obj (op V) => g • res M σ V := by
  classical
  choose U hxU hU using fun x : V => h x.1 x.2
  let W : V → X.Opens := fun x => V ⊓ U x
  have hWV : ∀ x, W x ≤ V := fun x => inf_le_left
  have hWU : ∀ x, W x ≤ U x := fun x => inf_le_right
  have hcover : V ≤ iSup W := fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, ⟨hy, hxU ⟨y, hy⟩⟩⟩
  constructor
  ·
    intro g₁ g₂ hg
    have hg' : g₁ • res M σ V = g₂ • res M σ V := hg
    apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf W V (fun x => homOfLE (hWV x)) hcover
    intro x
    apply (hU x (W x) (hWU x)).1
    show X.presheaf.map (homOfLE (hWV x)).op g₁ • res M σ (W x) = X.presheaf.map (homOfLE (hWV x)).op g₂ • res M σ (W x)
    rw [← smul_res, ← smul_res, hg']
  ·
    intro s
    have hloc : ∀ x, ∃! g : X.presheaf.obj (op (W x)), g • res M σ (W x) = M.presheaf.map (homOfLE (hWV x)).op s :=
      fun x => (Function.bijective_iff_existsUnique _).1 (hU x (W x) (hWU x)) _
    choose gx hgx _ using hloc
    have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj W gx := by
      intro x y
      apply (hU x (W x ⊓ W y) (inf_le_left.trans (hWU x))).1
      show X.presheaf.map (Opens.infLELeft (W x) (W y)).op (gx x) • res M σ (W x ⊓ W y) = X.presheaf.map (Opens.infLERight (W x) (W y)).op (gx y) • res M σ (W x ⊓ W y)
      rw [← smul_res M σ (Opens.infLELeft (W x) (W y)), hgx x, ← smul_res M σ (Opens.infLERight (W x) (W y)), hgx y, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
      rfl
    obtain ⟨g, hg, -⟩ : ∃! g : X.presheaf.obj (op V), ∀ x, X.presheaf.map (homOfLE (hWV x)).op g = gx x :=
      TopCat.Sheaf.existsUnique_gluing' X.sheaf W V (fun x => homOfLE (hWV x)) hcover gx hcompat
    refine ⟨g, ?_⟩
    apply TopCat.Sheaf.eq_of_locally_eq' (abSheaf M) W V (fun x => homOfLE (hWV x)) hcover
    intro x
    show M.presheaf.map (homOfLE (hWV x)).op (g • res M σ V) = M.presheaf.map (homOfLE (hWV x)).op s
    rw [smul_res, ← hgx x]
    apply congrArg (· • res M σ (W x)) (hg x)

/--
[AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type (u + 1))} (M : X.Modules)
  (σ : (Scheme.Modules.presheaf M).obj (op ⊤)) (V : X.Opens)
  (h : ∀ x ∈ V, ∃ U : X.Opens, x ∈ U ∧ ∀ W : X.Opens, W ≤ U → Function.Bijective fun g : X.presheaf.obj (op W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ : (Scheme.Modules.presheaf M).obj (op W))) :
    Function.Bijective fun g : X.presheaf.obj (op V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op σ : (Scheme.Modules.presheaf M).obj (op V)) :=
  helper_main M σ V h


-- created on 2026-10-20
