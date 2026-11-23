module

public import Mathlib
public import Instance.ModularForm_KatzLevelOne
public import Instance.ModularCurve_KatzLevelP
public import Structure.ModularCurve_KatzLevelP

public noncomputable section

set_option autoImplicit false

universe u v w

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

section Elements

variable {A : Type*} [CommRing A]


public theorem inLine_self (W : WeierstrassCurve A) {p : ℕ} (hp : 1 ≤ (p - 1) / 2) (x₀ : A) :
    InLine W p x₀ x₀ :=
  ⟨1, le_rfl, hp, by simp [WeierstrassCurve.ΨSq_one, WeierstrassCurve.Φ_one]⟩


public theorem indepElt_map {B : Type*} [CommRing B] (W : WeierstrassCurve A) (f : A →+* B) (p : ℕ)
    (x₀ x : A) : indepElt (W.map f) p (f x₀) (f x) = f (indepElt W p x₀ x) := by
  simp only [indepElt, map_prod, map_sub, map_mul, WeierstrassCurve.map_ΨSq,
    WeierstrassCurve.map_Φ, Polynomial.eval_map, Polynomial.eval₂_at_apply]


public theorem InLine.map {B : Type*} [CommRing B] {W : WeierstrassCurve A} (f : A →+* B) {p : ℕ}
    {x₀ x : A} (h : InLine W p x₀ x) : InLine (W.map f) p (f x₀) (f x) := by
  obtain ⟨a, ha, ha', hx⟩ := h
  refine ⟨a, ha, ha', ?_⟩
  rw [WeierstrassCurve.map_ΨSq, WeierstrassCurve.map_Φ, Polynomial.eval_map,
    Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval₂_at_apply, ← map_mul, hx]

end Elements


namespace LevelPData

variable {A : Type u} {B : Type v}


@[simp] public theorem swap_xP (D : LevelPData A) : D.swap.xP = D.xQ := rfl

@[simp] public theorem swap_yP (D : LevelPData A) : D.swap.yP = D.yQ := rfl

@[simp] public theorem swap_xQ (D : LevelPData A) : D.swap.xQ = D.xP := rfl

@[simp] public theorem swap_yQ (D : LevelPData A) : D.swap.yQ = D.yP := rfl


@[simp] public theorem swap_swap (D : LevelPData A) : D.swap.swap = D := rfl

variable [CommRing A] [CommRing B]


@[simp] public theorem map_xP (f : A →+* B) (D : LevelPData A) : (D.map f).xP = f D.xP := rfl

@[simp] public theorem map_yP (f : A →+* B) (D : LevelPData A) : (D.map f).yP = f D.yP := rfl

@[simp] public theorem map_xQ (f : A →+* B) (D : LevelPData A) : (D.map f).xQ = f D.xQ := rfl

@[simp] public theorem map_yQ (f : A →+* B) (D : LevelPData A) : (D.map f).yQ = f D.yQ := rfl


public theorem map_id (D : LevelPData A) : D.map (RingHom.id A) = D := rfl


public theorem map_map {C : Type w} [CommRing C] (f : A →+* B) (g : B →+* C) (D : LevelPData A) :
    (D.map f).map g = D.map (g.comp f) := rfl


public theorem map_swap (f : A →+* B) (D : LevelPData A) : D.swap.map f = (D.map f).swap := rfl


@[simp] public theorem variableChange_xP (C : VariableChange A) (D : LevelPData A) :
    (D.variableChange C).xP = ((C.u⁻¹ : Aˣ) : A) ^ 2 * (D.xP - C.r) := rfl

@[simp] public theorem variableChange_yP (C : VariableChange A) (D : LevelPData A) :
    (D.variableChange C).yP = ((C.u⁻¹ : Aˣ) : A) ^ 3 * (D.yP - C.s * (D.xP - C.r) - C.t) := rfl

@[simp] public theorem variableChange_xQ (C : VariableChange A) (D : LevelPData A) :
    (D.variableChange C).xQ = ((C.u⁻¹ : Aˣ) : A) ^ 2 * (D.xQ - C.r) := rfl

@[simp] public theorem variableChange_yQ (C : VariableChange A) (D : LevelPData A) :
    (D.variableChange C).yQ = ((C.u⁻¹ : Aˣ) : A) ^ 3 * (D.yQ - C.s * (D.xQ - C.r) - C.t) := rfl


public theorem variableChange_swap (C : VariableChange A) (D : LevelPData A) :
    D.swap.variableChange C = (D.variableChange C).swap := rfl

end LevelPData


namespace IsLevelPStructure

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] {W : WeierstrassCurve A} {p : ℕ}
  {D : LevelPData A}


public theorem swap (h : IsLevelPStructure W p D) : IsLevelPStructure W p D.swap :=
  ⟨h.equation_Q, h.equation_P, h.preΨ_Q, h.preΨ_P, h.isUnit_indepElt_QP, h.isUnit_indepElt_PQ⟩


public theorem map (h : IsLevelPStructure W p D) (f : A →+* B) :
    IsLevelPStructure (W.map f) p (D.map f) where
  equation_P := h.equation_P.map f
  equation_Q := h.equation_Q.map f
  preΨ_P := by
    rw [LevelPData.map_xP, WeierstrassCurve.map_preΨ, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, h.preΨ_P, map_zero]
  preΨ_Q := by
    rw [LevelPData.map_xQ, WeierstrassCurve.map_preΨ, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, h.preΨ_Q, map_zero]
  isUnit_indepElt_PQ := by
    rw [LevelPData.map_xP, LevelPData.map_xQ, indepElt_map]
    exact h.isUnit_indepElt_PQ.map f
  isUnit_indepElt_QP := by
    rw [LevelPData.map_xP, LevelPData.map_xQ, indepElt_map]
    exact h.isUnit_indepElt_QP.map f


public theorem equation_variableChange_aux (C : VariableChange A) {x y : A}
    (h : W.toAffine.Equation x y) :
    (C • W).toAffine.Equation (((C.u⁻¹ : Aˣ) : A) ^ 2 * (x - C.r))
      (((C.u⁻¹ : Aˣ) : A) ^ 3 * (y - C.s * (x - C.r) - C.t)) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆]
  linear_combination ((C.u⁻¹ : Aˣ) : A) ^ 6 * h


public theorem equation_P_variableChange (h : IsLevelPStructure W p D) (C : VariableChange A) :
    (C • W).toAffine.Equation (D.variableChange C).xP (D.variableChange C).yP :=
  equation_variableChange_aux C h.equation_P


public theorem equation_Q_variableChange (h : IsLevelPStructure W p D) (C : VariableChange A) :
    (C • W).toAffine.Equation (D.variableChange C).xQ (D.variableChange C).yQ :=
  equation_variableChange_aux C h.equation_Q

end IsLevelPStructure


namespace KatzLevelPForm

variable {R : Type u} [CommRing R] {p : ℕ} {k l : ℤ}


public theorem toFun_injective : Function.Injective (toFun : KatzLevelPForm R p k → _) := by
  rintro ⟨F, _, _⟩ ⟨G, _, _⟩ h
  congr


@[ext]
public theorem ext {F G : KatzLevelPForm R p k}
    (h : ∀ ⦃A : Type u⦄ [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
      (D : LevelPData A) (hD : IsLevelPStructure W p D), F.toFun W hW D hD = G.toFun W hW D hD) :
    F = G :=
  toFun_injective (by funext A _ _ W hW D hD; exact h W hW D hD)

section simp_lemmas

variable {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ)
  (D : LevelPData A) (hD : IsLevelPStructure W p D)


@[simp] public theorem zero_toFun : (0 : KatzLevelPForm R p k).toFun W hW D hD = 0 := rfl


@[simp] public theorem add_toFun (F G : KatzLevelPForm R p k) :
    (F + G).toFun W hW D hD = F.toFun W hW D hD + G.toFun W hW D hD := rfl


@[simp] public theorem neg_toFun (F : KatzLevelPForm R p k) :
    (-F).toFun W hW D hD = -F.toFun W hW D hD := rfl


@[simp] public theorem sub_toFun (F G : KatzLevelPForm R p k) :
    (F - G).toFun W hW D hD = F.toFun W hW D hD - G.toFun W hW D hD := rfl


@[simp] public theorem smul_toFun (c : R) (F : KatzLevelPForm R p k) :
    (c • F).toFun W hW D hD = c • F.toFun W hW D hD := rfl

end simp_lemmas


@[simp] public theorem mul_toFun (F : KatzLevelPForm R p k) (G : KatzLevelPForm R p l) {A : Type u}
    [CommRing A] [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A)
    (hD : IsLevelPStructure W p D) :
    (F.mul G).toFun W hW D hD = F.toFun W hW D hD * G.toFun W hW D hD := rfl


@[simp] public theorem swap_toFun (F : KatzLevelPForm R p k) {A : Type u} [CommRing A] [Algebra R A]
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A)
    (hD : IsLevelPStructure W p D) :
    F.swap.toFun W hW D hD = F.toFun W hW D.swap hD.swap := rfl


@[simp] public theorem swap_swap (F : KatzLevelPForm R p k) : F.swap.swap = F := rfl


@[simp] public theorem swap_zero : (0 : KatzLevelPForm R p k).swap = 0 := rfl


@[simp] public theorem swap_add (F G : KatzLevelPForm R p k) : (F + G).swap = F.swap + G.swap := rfl


@[simp] public theorem swap_neg (F : KatzLevelPForm R p k) : (-F).swap = -F.swap := rfl


@[simp] public theorem swap_sub (F G : KatzLevelPForm R p k) : (F - G).swap = F.swap - G.swap := rfl


@[simp] public theorem swap_smul (c : R) (F : KatzLevelPForm R p k) : (c • F).swap = c • F.swap := rfl


public theorem swapInvariant_iff_swap_eq (F : KatzLevelPForm R p k) : F.SwapInvariant ↔ F.swap = F :=
  ⟨fun h => ext fun _ _ _ W hW D hD => h W hW D hD,
    fun h A _ _ W hW D hD => by rw [← swap_toFun, h]⟩


public theorem DependsOnlyOnSndLine.dependsOnlyOnLines {F : KatzLevelPForm R p k}
    (h : F.DependsOnlyOnSndLine) : F.DependsOnlyOnLines :=
  fun _ _ _ W hW D D' hD hD' _ hQ => h W hW D D' hD hD' hQ


public theorem DependsOnlyOnSndLine.dependsOnlyOnLines_swap_sub {F : KatzLevelPForm R p k}
    (h : F.DependsOnlyOnSndLine) : (F.swap - F).DependsOnlyOnLines := by
  intro A _ _ W hW D D' hD hD' hP hQ
  simp only [sub_toFun, swap_toFun]
  rw [h W hW D D' hD hD' hQ, h W hW D.swap D'.swap hD.swap hD'.swap hP]


public theorem DependsOnlyOnSndLine.zero : (0 : KatzLevelPForm R p k).DependsOnlyOnSndLine :=
  fun _ _ _ _ _ _ _ _ _ _ => rfl


public theorem DependsOnlyOnSndLine.add {F G : KatzLevelPForm R p k} (hF : F.DependsOnlyOnSndLine)
    (hG : G.DependsOnlyOnSndLine) : (F + G).DependsOnlyOnSndLine := by
  intro A _ _ W hW D D' hD hD' hQ
  simp only [add_toFun, hF W hW D D' hD hD' hQ, hG W hW D D' hD hD' hQ]


public theorem DependsOnlyOnSndLine.neg {F : KatzLevelPForm R p k} (hF : F.DependsOnlyOnSndLine) :
    (-F).DependsOnlyOnSndLine := by
  intro A _ _ W hW D D' hD hD' hQ
  simp only [neg_toFun, hF W hW D D' hD hD' hQ]


public theorem DependsOnlyOnSndLine.smul (c : R) {F : KatzLevelPForm R p k}
    (hF : F.DependsOnlyOnSndLine) : (c • F).DependsOnlyOnSndLine := by
  intro A _ _ W hW D D' hD hD' hQ
  simp only [smul_toFun, hF W hW D D' hD hD' hQ]


public theorem DependsOnlyOnSndLine.mul {F : KatzLevelPForm R p k} {G : KatzLevelPForm R p l}
    (hF : F.DependsOnlyOnSndLine) (hG : G.DependsOnlyOnSndLine) :
    (F.mul G).DependsOnlyOnSndLine := by
  intro A _ _ W hW D D' hD hD' hQ
  simp only [mul_toFun, hF W hW D D' hD hD' hQ, hG W hW D D' hD hD' hQ]

end KatzLevelPForm


namespace KatzGamma0Form

variable {R : Type u} [CommRing R] {p : ℕ} {k l : ℤ}


public theorem toKatzLevelPForm_injective :
    Function.Injective (toKatzLevelPForm : KatzGamma0Form R p k → KatzLevelPForm R p k) := by
  rintro ⟨F, _⟩ ⟨G, _⟩ h
  congr


@[ext]
public theorem ext {F G : KatzGamma0Form R p k} (h : F.toKatzLevelPForm = G.toKatzLevelPForm) : F = G :=
  toKatzLevelPForm_injective h


@[simp] public theorem toKatzLevelPForm_zero : (0 : KatzGamma0Form R p k).toKatzLevelPForm = 0 := rfl

@[simp] public theorem toKatzLevelPForm_add (F G : KatzGamma0Form R p k) :
    (F + G).toKatzLevelPForm = F.toKatzLevelPForm + G.toKatzLevelPForm := rfl

@[simp] public theorem toKatzLevelPForm_neg (F : KatzGamma0Form R p k) :
    (-F).toKatzLevelPForm = -F.toKatzLevelPForm := rfl

@[simp] public theorem toKatzLevelPForm_sub (F G : KatzGamma0Form R p k) :
    (F - G).toKatzLevelPForm = F.toKatzLevelPForm - G.toKatzLevelPForm := rfl

@[simp] public theorem toKatzLevelPForm_smul (c : R) (F : KatzGamma0Form R p k) :
    (c • F).toKatzLevelPForm = c • F.toKatzLevelPForm := rfl


@[simp] public theorem toKatzLevelPForm_mul (F : KatzGamma0Form R p k) (G : KatzGamma0Form R p l) :
    (F.mul G).toKatzLevelPForm = F.toKatzLevelPForm.mul G.toKatzLevelPForm := rfl

end KatzGamma0Form

end ModularCurve

namespace KatzModularForm

variable {R : Type u} [CommRing R] {k : ℤ}


@[simp] public theorem pullbackLevelP_toFun (g : KatzModularForm R k) (p : ℕ) {A : Type u} [CommRing A]
    [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : ModularCurve.LevelPData A)
    (hD : ModularCurve.IsLevelPStructure W p D) :
    (g.pullbackLevelP p).toFun W hW D hD = g.toFun W hW := rfl


public theorem dependsOnlyOnSndLine_pullbackLevelP (g : KatzModularForm R k) (p : ℕ) :
    (g.pullbackLevelP p).DependsOnlyOnSndLine :=
  fun _ _ _ _ _ _ _ _ _ _ => rfl


public theorem swapInvariant_pullbackLevelP (g : KatzModularForm R k) (p : ℕ) :
    (g.pullbackLevelP p).SwapInvariant :=
  fun _ _ _ _ _ _ _ => rfl


@[simp] public theorem swap_pullbackLevelP (g : KatzModularForm R k) (p : ℕ) :
    (g.pullbackLevelP p).swap = g.pullbackLevelP p := rfl


@[simp] public theorem pullbackGamma0_toKatzLevelPForm (g : KatzModularForm R k) (p : ℕ) :
    (g.pullbackGamma0 p).toKatzLevelPForm = g.pullbackLevelP p := rfl


@[simp] public theorem pullbackLevelP_zero (p : ℕ) : (0 : KatzModularForm R k).pullbackLevelP p = 0 :=
  rfl


@[simp] public theorem pullbackLevelP_add (g h : KatzModularForm R k) (p : ℕ) :
    (g + h).pullbackLevelP p = g.pullbackLevelP p + h.pullbackLevelP p := rfl


@[simp] public theorem pullbackLevelP_smul (c : R) (g : KatzModularForm R k) (p : ℕ) :
    (c • g).pullbackLevelP p = c • g.pullbackLevelP p := rfl

end KatzModularForm

namespace ModularCurve.LevelP

variable (p : ℕ)


@[simp] public theorem coe_unipotentU :
    (unipotentU p : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 1; 0, 1] := rfl


@[simp] public theorem coe_swapW : (swapW p : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![0, 1; 1, 0] := rfl


public theorem mem_borel_iff (g : GL (Fin 2) (ZMod p)) :
    g ∈ borel p ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 := Iff.rfl


public theorem mem_splitTorus_iff (g : GL (Fin 2) (ZMod p)) :
    g ∈ splitTorus p ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 ∧
      (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := Iff.rfl


public theorem splitTorus_le_borel : splitTorus p ≤ borel p := fun _ hg => hg.1

end ModularCurve.LevelP

end
