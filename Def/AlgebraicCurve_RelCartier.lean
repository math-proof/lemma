import Lemma.AlgebraicGeometry.IdealSheafHom
import Lemma.AlgebraicCurve.UniversalDivisor

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

def IsInvertible (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ (U : X.affineOpens) (f : Γ(X, U)), x ∈ X.basicOpen f ∧
    ∃ g ∈ nonZeroDivisors Γ(X, X.affineBasicOpen f), I.ideal (X.affineBasicOpen f) = Ideal.span {g}

theorem isInvertible_top : (⊤ : X.IdealSheafData).IsInvertible := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine ⟨⟨U, hU⟩, 1, by simpa using hxU, 1, one_mem _, ?_⟩
  rw [ideal_top, Pi.top_apply, Ideal.span_singleton_one]

theorem IsInvertible.mul {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    (I * J).IsInvertible := by
  intro x
  obtain ⟨U, f, hxf, g, hg, hIg⟩ := hI x
  obtain ⟨U', f', hxf', g', hg', hJg⟩ := hJ x

  obtain ⟨h, h', hhh', hxh⟩ := exists_basicOpen_le_affine_inter (X.affineBasicOpen f).2
    (X.affineBasicOpen f').2 x ⟨hxf, hxf'⟩
  have hW : (X.affineBasicOpen h : X.Opens) ≤ X.affineBasicOpen f := X.basicOpen_le h
  have hW' : (X.affineBasicOpen h : X.Opens) ≤ X.affineBasicOpen f' :=
    hhh'.trans_le (X.basicOpen_le h')
  refine ⟨X.affineBasicOpen f, h, hxh, ((X.presheaf.map (homOfLE hW).op).hom g :
    Γ(X, X.affineBasicOpen h)) * (X.presheaf.map (homOfLE hW').op).hom g', mul_mem ?_ ?_, ?_⟩
  ·
    letI := (X.affineBasicOpen f).2.isLocalization_basicOpen h
    exact IsLocalization.nonZeroDivisors_le_comap (M := .powers h)
      (S := Γ(X, X.basicOpen h)) hg
  ·
    letI := (X.presheaf.map (homOfLE hW').op).hom.toAlgebra
    haveI := (X.affineBasicOpen f').2.isLocalization_of_eq_basicOpen h' (homOfLE hW') hhh'
    exact IsLocalization.nonZeroDivisors_le_comap (M := .powers h')
      (S := Γ(X, X.affineBasicOpen h)) hg'
  · rw [ideal_mul, Pi.mul_apply,
      ← I.map_ideal (U := X.affineBasicOpen h) (V := X.affineBasicOpen f) hW, hIg,
      ← J.map_ideal (U := X.affineBasicOpen h) (V := X.affineBasicOpen f') hW', hJg,
      Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_mul_span_singleton]
    rfl

namespace IdealHom

variable {X' : Scheme.{u}} (f : X' ⟶ X) {I J : X.IdealSheafData}

theorem appLE_mem_comap_ideal (U : X.affineOpens) (U' : X'.affineOpens)
    (h : (U' : X'.Opens) ≤ f ⁻¹ᵁ U) (x : I.ideal U) :
    f.appLE U U' h x ∈ (I.comap f).ideal U' := by

  have hx : (x : Γ(X, U)) ∈ ((I.comap f).map f).ideal U := (le_def.mp (I.le_map_comap f)) U x.2
  have h0 : ((I.comap f).subschemeι ≫ f).app U x = 0 :=
    RingHom.mem_ker.mp (Scheme.Hom.ideal_ker_le _ U hx)

  have key : (I.comap f).ideal U' = RingHom.ker ((I.comap f).subschemeι.app U').hom := by
    conv_lhs => rw [← (I.comap f).ker_subschemeι]
    exact Scheme.Hom.ker_apply _ U'
  rw [key, RingHom.mem_ker, Scheme.Hom.appLE, CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.naturality, CommRingCat.comp_apply]
  have h0' : (I.comap f).subschemeι.app (f ⁻¹ᵁ U) (f.app U x) = 0 := h0
  rw [h0', map_zero]

def IsBaseChangeAlong (φ : IdealHom I J) (φ' : IdealHom (I.comap f) (J.comap f)) : Prop :=
  ∀ (U : X.affineOpens) (U' : X'.affineOpens) (h : (U' : X'.Opens) ≤ f ⁻¹ᵁ U) (x : I.ideal U),
    (φ'.app U' ⟨f.appLE U U' h x, appLE_mem_comap_ideal f U U' h x⟩ : Γ(X', U')) =
      f.appLE U U' h (φ.app U x)

end IdealHom

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicCurve

open AlgebraicGeometry Scheme.IdealSheafData

variable {k : Type u} [Field k] {C : Scheme.{u}} {c : C ⟶ Spec (.of k)}

def RelEffDivisor.IsCartier {d : ℕ} {T : Scheme.{u}} {t : T ⟶ Spec (.of k)}
    (Z : RelEffDivisor C c d T t) : Prop :=
  Z.I.IsInvertible

noncomputable def RelEffDivisor.const {r : ℕ}
    (D : RelEffDivisor C c r (Spec (.of k)) (𝟙 _)) {T : Scheme.{u}} (t : T ⟶ Spec (.of k)) :
    RelEffDivisor C c r T t :=
  D.pullbackAlong t (Category.comp_id t)

def IdealHom.FibrewiseNonvanishing (c : C ⟶ Spec (.of k)) {T : Scheme.{u}}
    (t : T ⟶ Spec (.of k)) {I J : (pullback c t).IdealSheafData} (φ : IdealHom I J) : Prop :=
  ∀ s : T, ∃ φ' : IdealHom (I.comap (mapOnProd c (T.fromSpecResidueField s) rfl))
      (J.comap (mapOnProd c (T.fromSpecResidueField s) rfl)),
    φ.IsBaseChangeAlong (mapOnProd c (T.fromSpecResidueField s) rfl) φ' ∧ φ' ≠ 0

end AlgebraicCurve
