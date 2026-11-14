import Mathlib
import Abbrev.CategoryTheory_OverTotalPresheaf

set_option autoImplicit false

open CategoryTheory Category Opposite

namespace CategoryTheory.Functor

universe w v u

variable {C : Type u} [Category.{v} C] {S : C} (G : (Over S)ᵒᵖ ⥤ Type w)

@[implicit_reducible]
def overTotal : Cᵒᵖ ⥤ Type (max w v) where
  obj T := G.OverTotal T.unop
  map {T T'} φ := TypeCat.ofHom fun a =>
    ⟨φ.unop ≫ a.1, G.map (Over.homMk φ.unop rfl : Over.mk (φ.unop ≫ a.1) ⟶ Over.mk a.1).op a.2⟩
  map_id T := by
    have map_op_apply_eq_of_left_eq {A B : Over S} (k k' : A ⟶ B) (h : k.left = k'.left)
        (x : G.obj (op B)) : G.map k.op x = G.map k'.op x := by
      rw [Over.OverMorphism.ext h]
    have map_op_apply_eq_self {A : Over S} (k : A ⟶ A) (h : k.left = 𝟙 _) (x : G.obj (op A)) :
        G.map k.op x = x := by
      rw [show k = 𝟙 A from Over.OverMorphism.ext (by simpa using h), op_id, Functor.map_id_apply]
    have map_op_map_op_apply {A B B' : Over S} (k : A ⟶ B) (k' : B ⟶ B') (x : G.obj (op B')) :
        G.map k.op (G.map k'.op x) = G.map (k ≫ k').op x := by
      rw [op_comp, Functor.map_comp_apply]
    have map_op_map_op_apply_eq_self {A B : Over S} (k : A ⟶ B) (k' : B ⟶ A)
        (h : (k ≫ k').left = 𝟙 _) (x : G.obj (op A)) :
        G.map k.op (G.map k'.op x) = x := by
      rw [map_op_map_op_apply]
      exact map_op_apply_eq_self (k ≫ k') h x
    have map_op_map_op_apply_eq {A B B' D : Over S} (k : A ⟶ B) (k' : B ⟶ B') (l : A ⟶ D)
        (l' : D ⟶ B') (h : (k ≫ k').left = (l ≫ l').left) (x : G.obj (op B')) :
        G.map k.op (G.map k'.op x) = G.map l.op (G.map l'.op x) := by
      rw [map_op_map_op_apply, map_op_map_op_apply]
      exact map_op_apply_eq_of_left_eq (k ≫ k') (l ≫ l') h x
    have OverTotal_ext' {T : C} {a b : G.OverTotal T} (h₁ : a.1 = b.1)
        (h₂ : G.map (Over.homMk (𝟙 T) (by simp [h₁]) : Over.mk b.1 ⟶ Over.mk a.1).op a.2 = b.2) :
        a = b := by
      obtain ⟨t, x⟩ := a
      obtain ⟨t', y⟩ := b
      obtain rfl : t = t' := h₁
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
      dsimp only at h₂
      rw [← h₂]
      symm
      exact map_op_apply_eq_self _ (by
        first | rfl | simp only [Over.comp_left]) x
    apply TypeCat.homEquiv.injective
    funext a
    refine OverTotal_ext' (by simp) ?_
    exact map_op_map_op_apply_eq_self _ _
      (by
        simp only [Over.comp_left]
        first | rfl | exact Category.id_comp _ | simp [Category.id_comp, Category.comp_id]) _
  map_comp {T T' T''} φ ψ := by
    have map_op_apply_eq_of_left_eq {A B : Over S} (k k' : A ⟶ B) (h : k.left = k'.left)
        (x : G.obj (op B)) : G.map k.op x = G.map k'.op x := by
      rw [Over.OverMorphism.ext h]
    have map_op_apply_eq_self {A : Over S} (k : A ⟶ A) (h : k.left = 𝟙 _) (x : G.obj (op A)) :
        G.map k.op x = x := by
      rw [show k = 𝟙 A from Over.OverMorphism.ext (by simpa using h), op_id, Functor.map_id_apply]
    have map_op_map_op_apply {A B B' : Over S} (k : A ⟶ B) (k' : B ⟶ B') (x : G.obj (op B')) :
        G.map k.op (G.map k'.op x) = G.map (k ≫ k').op x := by
      rw [op_comp, Functor.map_comp_apply]
    have map_op_map_op_apply_eq_self {A B : Over S} (k : A ⟶ B) (k' : B ⟶ A)
        (h : (k ≫ k').left = 𝟙 _) (x : G.obj (op A)) :
        G.map k.op (G.map k'.op x) = x := by
      rw [map_op_map_op_apply]
      exact map_op_apply_eq_self (k ≫ k') h x
    have map_op_map_op_apply_eq {A B B' D : Over S} (k : A ⟶ B) (k' : B ⟶ B') (l : A ⟶ D)
        (l' : D ⟶ B') (h : (k ≫ k').left = (l ≫ l').left) (x : G.obj (op B')) :
        G.map k.op (G.map k'.op x) = G.map l.op (G.map l'.op x) := by
      rw [map_op_map_op_apply, map_op_map_op_apply]
      exact map_op_apply_eq_of_left_eq (k ≫ k') (l ≫ l') h x
    have OverTotal_ext' {T : C} {a b : G.OverTotal T} (h₁ : a.1 = b.1)
        (h₂ : G.map (Over.homMk (𝟙 T) (by simp [h₁]) : Over.mk b.1 ⟶ Over.mk a.1).op a.2 = b.2) :
        a = b := by
      obtain ⟨t, x⟩ := a
      obtain ⟨t', y⟩ := b
      obtain rfl : t = t' := h₁
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
      dsimp only at h₂
      rw [← h₂]
      symm
      exact map_op_apply_eq_self _ (by
        first | rfl | simp only [Over.comp_left]) x
    apply TypeCat.homEquiv.injective
    funext a
    refine OverTotal_ext' (by simp) ?_
    exact map_op_map_op_apply_eq _ _ _ _
      (by
        simp only [Over.comp_left]
        first | rfl | exact Category.id_comp _ | simp [Category.id_comp, Category.comp_id]) _

variable {G}

def OverTotal.toFibre (T : Over S) (b : G.OverTotal T.left) (hb : b.1 = T.hom) : G.obj (op T) :=
  G.map (Over.homMk (𝟙 T.left) (by simpa using hb) : T ⟶ Over.mk b.1).op b.2

@[implicit_reducible]
def OverTotal.ofFibre (T : Over S) (x : G.obj (op T)) : G.OverTotal T.left :=
  ⟨T.hom, G.map (Over.homMk (𝟙 T.left) (by simp) : Over.mk T.hom ⟶ T).op x⟩

namespace RepresentableBy

variable {Y : C} (e : G.overTotal.RepresentableBy Y)

def overTotalBase : Y ⟶ S := (e.homEquiv (𝟙 Y)).1

noncomputable def ofOverTotal : G.RepresentableBy (Over.mk e.overTotalBase) where
  homEquiv {T} :=
    { toFun := fun g =>
        have overTotal_homEquiv_fst {T : C} (k : T ⟶ Y) :
            (e.homEquiv k).1 = k ≫ e.overTotalBase := by
          have h := e.homEquiv_comp k (𝟙 Y)
          rw [comp_id] at h
          rw [h]
          rfl
        OverTotal.toFibre T (e.homEquiv g.left)
          (by rw [overTotal_homEquiv_fst]; exact Over.w g)
      invFun := fun x =>
        have overTotal_homEquiv_fst {T : C} (k : T ⟶ Y) :
            (e.homEquiv k).1 = k ≫ e.overTotalBase := by
          have h := e.homEquiv_comp k (𝟙 Y)
          rw [comp_id] at h
          rw [h]
          rfl
        Over.homMk (e.homEquiv.symm (OverTotal.ofFibre T x)) (by
          have h := overTotal_homEquiv_fst (e.homEquiv.symm (OverTotal.ofFibre T x))
          have hz := Equiv.apply_symm_apply e.homEquiv (OverTotal.ofFibre T x)
          rw [hz] at h
          simpa [OverTotal.ofFibre, Over.mk_hom] using h.symm)
      left_inv := fun g => by
        have overTotal_homEquiv_fst {T : C} (k : T ⟶ Y) :
            (e.homEquiv k).1 = k ≫ e.overTotalBase := by
          have h := e.homEquiv_comp k (𝟙 Y)
          rw [comp_id] at h
          rw [h]
          rfl
        have map_op_apply_eq_of_left_eq {A B : Over S} (k k' : A ⟶ B) (h : k.left = k'.left)
            (x : G.obj (op B)) : G.map k.op x = G.map k'.op x := by
          rw [Over.OverMorphism.ext h]
        have map_op_apply_eq_self {A : Over S} (k : A ⟶ A) (h : k.left = 𝟙 _) (x : G.obj (op A)) :
            G.map k.op x = x := by
          rw [show k = 𝟙 A from Over.OverMorphism.ext (by simpa using h), op_id,
            Functor.map_id_apply]
        have map_op_map_op_apply {A B B' : Over S} (k : A ⟶ B) (k' : B ⟶ B') (x : G.obj (op B')) :
            G.map k.op (G.map k'.op x) = G.map (k ≫ k').op x := by
          rw [op_comp, Functor.map_comp_apply]
        have map_op_map_op_apply_eq_self {A B : Over S} (k : A ⟶ B) (k' : B ⟶ A)
            (h : (k ≫ k').left = 𝟙 _) (x : G.obj (op A)) :
            G.map k.op (G.map k'.op x) = x := by
          rw [map_op_map_op_apply]
          exact map_op_apply_eq_self (k ≫ k') h x
        have map_op_map_op_map_op_apply_eq_self {A B B' : Over S} (k : A ⟶ B) (k' : B ⟶ B')
            (k'' : B' ⟶ A) (h : (k ≫ k' ≫ k'').left = 𝟙 _) (x : G.obj (op A)) :
            G.map k.op (G.map k'.op (G.map k''.op x)) = x := by
          rw [map_op_map_op_apply, map_op_map_op_apply]
          rw [Category.assoc k k' k'']; exact map_op_apply_eq_self (k ≫ k' ≫ k'') h x
        have OverTotal_ext' {T : C} {a b : G.OverTotal T} (h₁ : a.1 = b.1)
            (h₂ : G.map (Over.homMk (𝟙 T) (by simp [h₁]) : Over.mk b.1 ⟶ Over.mk a.1).op a.2 = b.2) :
            a = b := by
          obtain ⟨t, x⟩ := a
          obtain ⟨t', y⟩ := b
          obtain rfl : t = t' := h₁
          simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
          dsimp only at h₂
          rw [← h₂]
          symm
          exact map_op_apply_eq_self _ (by
        first | rfl | simp only [Over.comp_left]) x
        have OverTotal_ofFibre_toFibre (T : Over S) (b : G.OverTotal T.left) (hb : b.1 = T.hom) :
            OverTotal.ofFibre T (OverTotal.toFibre T b hb) = b :=
          OverTotal_ext' (by simpa [OverTotal.ofFibre] using hb.symm)
            (map_op_map_op_map_op_apply_eq_self _ _ _
              (by
        simp only [Over.comp_left]
        first | rfl | exact Category.id_comp _ | simp [Category.id_comp, Category.comp_id]) _)
        apply Over.OverMorphism.ext
        simp only [Over.homMk_left]
        apply e.homEquiv.injective
        rw [Equiv.apply_symm_apply]
        exact OverTotal_ofFibre_toFibre T (e.homEquiv g.left) _
      right_inv := fun x => by
        have map_op_apply_eq_of_left_eq {A B : Over S} (k k' : A ⟶ B) (h : k.left = k'.left)
            (x : G.obj (op B)) : G.map k.op x = G.map k'.op x := by
          rw [Over.OverMorphism.ext h]
        have map_op_apply_eq_self {A : Over S} (k : A ⟶ A) (h : k.left = 𝟙 _) (x : G.obj (op A)) :
            G.map k.op x = x := by
          rw [show k = 𝟙 A from Over.OverMorphism.ext (by simpa using h), op_id,
            Functor.map_id_apply]
        have map_op_map_op_apply {A B B' : Over S} (k : A ⟶ B) (k' : B ⟶ B') (x : G.obj (op B')) :
            G.map k.op (G.map k'.op x) = G.map (k ≫ k').op x := by
          rw [op_comp, Functor.map_comp_apply]
        have map_op_map_op_apply_eq_self {A B : Over S} (k : A ⟶ B) (k' : B ⟶ A)
            (h : (k ≫ k').left = 𝟙 _) (x : G.obj (op A)) :
            G.map k.op (G.map k'.op x) = x := by
          rw [map_op_map_op_apply]
          exact map_op_apply_eq_self (k ≫ k') h x
        have OverTotal_toFibre_congr (T : Over S) {b b' : G.OverTotal T.left} (h : b = b')
            (hb : b.1 = T.hom) (hb' : b'.1 = T.hom) :
            OverTotal.toFibre T b hb = OverTotal.toFibre T b' hb' := by
          subst h; rfl
        have OverTotal_ofFibre_fst (T : Over S) (x : G.obj (op T)) :
            (OverTotal.ofFibre T x).1 = T.hom := rfl
        have OverTotal_toFibre_ofFibre (T : Over S) (x : G.obj (op T)) :
            OverTotal.toFibre T (OverTotal.ofFibre T x) (OverTotal_ofFibre_fst T x) = x :=
          map_op_map_op_apply_eq_self _ _
            (by
        simp only [Over.comp_left]
        first | rfl | exact Category.id_comp _ | simp [Category.id_comp, Category.comp_id]) x
        exact (OverTotal_toFibre_congr T
            (Equiv.apply_symm_apply e.homEquiv (OverTotal.ofFibre T x)) _ (OverTotal_ofFibre_fst T x)).trans
          (OverTotal_toFibre_ofFibre T x) }
  homEquiv_comp {T T'} φ g := by
    have overTotal_map_fst {T T' : Cᵒᵖ} (φ : T ⟶ T') (a : G.overTotal.obj T) :
        (G.overTotal.map φ a).1 = φ.unop ≫ a.1 := rfl
    have overTotal_homEquiv_fst {T : C} (k : T ⟶ Y) : (e.homEquiv k).1 = k ≫ e.overTotalBase := by
      have h := e.homEquiv_comp k (𝟙 Y)
      rw [comp_id] at h
      rw [h]
      rfl
    have OverTotal_toFibre_congr (T : Over S) {b b' : G.OverTotal T.left} (h : b = b')
        (hb : b.1 = T.hom) (hb' : b'.1 = T.hom) :
        OverTotal.toFibre T b hb = OverTotal.toFibre T b' hb' := by
      subst h; rfl
    have map_op_apply_eq_of_left_eq {A B : Over S} (k k' : A ⟶ B) (h : k.left = k'.left)
        (x : G.obj (op B)) : G.map k.op x = G.map k'.op x := by
      rw [Over.OverMorphism.ext h]
    have map_op_map_op_apply {A B B' : Over S} (k : A ⟶ B) (k' : B ⟶ B') (x : G.obj (op B')) :
        G.map k.op (G.map k'.op x) = G.map (k ≫ k').op x := by
      rw [op_comp, Functor.map_comp_apply]
    have map_op_map_op_apply_eq {A B B' D : Over S} (k : A ⟶ B) (k' : B ⟶ B') (l : A ⟶ D)
        (l' : D ⟶ B') (h : (k ≫ k').left = (l ≫ l').left) (x : G.obj (op B')) :
        G.map k.op (G.map k'.op x) = G.map l.op (G.map l'.op x) := by
      rw [map_op_map_op_apply, map_op_map_op_apply]
      exact map_op_apply_eq_of_left_eq (k ≫ k') (l ≫ l') h x
    have OverTotal_toFibre_naturality {T T' : Over S} (φ : T ⟶ T') (b : G.OverTotal T'.left)
        (hb : b.1 = T'.hom) (hb' : (G.overTotal.map φ.left.op b).1 = T.hom) :
        OverTotal.toFibre T (G.overTotal.map φ.left.op b) hb' =
          G.map φ.op (OverTotal.toFibre T' b hb) :=
      map_op_map_op_apply_eq _ _ _ _
        (by
        simp only [Over.comp_left]
        first | rfl | exact Category.id_comp _ | simp [Category.id_comp, Category.comp_id]) _
    have hg : (e.homEquiv g.left).1 = T'.hom := by
      rw [overTotal_homEquiv_fst]; exact Over.w g
    have hφg : (e.homEquiv (φ ≫ g).left).1 = T.hom := by
      rw [overTotal_homEquiv_fst]; exact Over.w (φ ≫ g)
    have hb' : (G.overTotal.map φ.left.op (e.homEquiv g.left)).1 = T.hom := by
      rw [overTotal_map_fst, overTotal_homEquiv_fst, Quiver.Hom.unop_op, ← assoc]
      exact Over.w (φ ≫ g)
    calc OverTotal.toFibre T (e.homEquiv (φ ≫ g).left) hφg
        = OverTotal.toFibre T (G.overTotal.map φ.left.op (e.homEquiv g.left)) hb' :=
          OverTotal_toFibre_congr T (e.homEquiv_comp φ.left g.left) hφg hb'
      _ = G.map φ.op (OverTotal.toFibre T' (e.homEquiv g.left) hg) :=
          OverTotal_toFibre_naturality φ _ hg hb'

end RepresentableBy

end CategoryTheory.Functor
