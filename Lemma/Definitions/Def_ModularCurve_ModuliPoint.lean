import Mathlib
import Lemma.Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Lemma.Definitions.Def_WeierstrassCurve_RatPointHom

noncomputable section

namespace ModularCurve

open WeierstrassCurve WeierstrassCurve.Affine

section Pairs

variable (N : ℕ) (L : Type*) [Field L] [DecidableEq L]

structure Gamma0Pair where

  toCurve : WeierstrassCurve L

  isElliptic : toCurve.IsElliptic

  gen : toCurve.toAffine.Point

  addOrderOf_gen : addOrderOf gen = N

attribute [instance] Gamma0Pair.isElliptic

variable {N L}

def Gamma0Pair.Step (P Q : Gamma0Pair N L) : Prop :=
  ∃ γ : VariableChange L, ∃ _ : γ • P.toCurve = Q.toCurve, ∃ k : ℕ, k.Coprime N ∧
    HEq Q.gen (k • Point.vcInvFun γ P.toCurve.toAffine P.gen)

variable (N L) in

def ModuliPoint : Type _ := Quot (Gamma0Pair.Step (N := N) (L := L))

noncomputable def ModuliPoint.j : ModuliPoint N L → L :=
  Quot.lift (fun P => P.toCurve.j) fun P Q h => by
    obtain ⟨γ, hγ, -⟩ := h
    show P.toCurve.j = Q.toCurve.j
    simp_rw [← hγ, variableChange_j]

@[simp] lemma ModuliPoint.j_mk (P : Gamma0Pair N L) :
    ModuliPoint.j (Quot.mk _ P : ModuliPoint N L) = P.toCurve.j := rfl

end Pairs

section HEqToolbox

variable {K : Type*} [Field K]

theorem Point.heq_zero {V V' : WeierstrassCurve.Affine K} (hV : V' = V) :
    HEq (0 : V'.Point) (0 : V.Point) := by
  subst hV
  rfl

theorem Point.heq_some {V V' : WeierstrassCurve.Affine K} (hV : V' = V) {x y x' y' : K}
    {h : V.Nonsingular x y} {h' : V'.Nonsingular x' y'} (hx : x' = x) (hy : y' = y) :
    HEq (Point.some x' y' h' : V'.Point) (Point.some x y h : V.Point) := by
  subst hV
  subst hx
  subst hy
  rfl

theorem Point.heq_nsmul [DecidableEq K] {V V' : WeierstrassCurve.Affine K} (hV : V' = V)
    (n : ℕ) {S : V'.Point} {T : V.Point} (h : HEq S T) : HEq (n • S) (n • T) := by
  subst hV
  rw [eq_of_heq h]

end HEqToolbox

section Map

variable {L L' : Type} [Field L] [Field L']
variable [DecidableEq L] [DecidableEq L']

theorem addOrderOf_ratPointMap (σ : L →+* L') (V : WeierstrassCurve L) (P : V.toAffine.Point) :
    addOrderOf (WeierstrassCurve.ratPointMap σ (W₀ := V) P) = addOrderOf P :=
  addOrderOf_injective (WeierstrassCurve.ratPointHom σ (W₀ := V))
    (WeierstrassCurve.ratPointMap_injective σ (W₀ := V)) P

theorem ratPointMap_nsmul (σ : L →+* L') (V : WeierstrassCurve L) (k : ℕ) (P : V.toAffine.Point) :
    WeierstrassCurve.ratPointMap σ (W₀ := V) (k • P) = k • WeierstrassCurve.ratPointMap σ (W₀ := V) P :=
  map_nsmul (WeierstrassCurve.ratPointHom σ (W₀ := V)) k P

omit [DecidableEq L] [DecidableEq L'] in

theorem map_vcXInv (σ : L →+* L') (γ : VariableChange L) (x : L) :
    σ (vcXInv γ x) = vcXInv (γ.map σ) (σ x) := by
  simp [vcXInv, map_mul, map_pow, map_sub]

omit [DecidableEq L] [DecidableEq L'] in

theorem map_vcYInv (σ : L →+* L') (γ : VariableChange L) (x y : L) :
    σ (vcYInv γ x y) = vcYInv (γ.map σ) (σ x) (σ y) := by
  simp [vcYInv, map_mul, map_pow, map_sub]

omit [DecidableEq L] [DecidableEq L'] in

theorem ratPointMap_vcInvFun_heq (σ : L →+* L') (γ : VariableChange L) (V : WeierstrassCurve L)
    (P : V.toAffine.Point) :
    HEq (WeierstrassCurve.ratPointMap σ (W₀ := γ • V) (Point.vcInvFun γ V.toAffine P))
        (Point.vcInvFun (γ.map σ) (V.map σ).toAffine (WeierstrassCurve.ratPointMap σ (W₀ := V) P)) := by
  have hc : (γ • V).map σ = (γ.map σ) • (V.map σ) :=
    (WeierstrassCurve.map_variableChange V γ σ).symm
  cases P with
  | zero => exact Point.heq_zero hc
  | some x y h => exact Point.heq_some hc (map_vcXInv σ γ x) (map_vcYInv σ γ x y)

variable {N : ℕ}

def gamma0PairMap (σ : L →+* L') (P : Gamma0Pair N L) : Gamma0Pair N L' where
  toCurve := P.toCurve.map σ
  isElliptic := inferInstance
  gen := WeierstrassCurve.ratPointMap σ (W₀ := P.toCurve) P.gen
  addOrderOf_gen := (addOrderOf_ratPointMap σ P.toCurve P.gen).trans P.addOrderOf_gen

@[simp] theorem gamma0PairMap_toCurve (σ : L →+* L') (P : Gamma0Pair N L) :
    (gamma0PairMap σ P).toCurve = P.toCurve.map σ := rfl

@[simp] theorem gamma0PairMap_gen (σ : L →+* L') (P : Gamma0Pair N L) :
    (gamma0PairMap σ P).gen = WeierstrassCurve.ratPointMap σ (W₀ := P.toCurve) P.gen := rfl

theorem gamma0PairStep_map (σ : L →+* L') {P Q : Gamma0Pair N L}
    (h : Gamma0Pair.Step P Q) :
    Gamma0Pair.Step (gamma0PairMap σ P) (gamma0PairMap σ Q) := by
  obtain ⟨γ, hγ, k, hk, hgen⟩ := h
  obtain ⟨WP, hEP, gP, hgP⟩ := P
  obtain ⟨WQ, hEQ, gQ, hgQ⟩ := Q
  change γ • WP = WQ at hγ
  subst hγ
  change HEq gQ (k • Point.vcInvFun γ WP.toAffine gP) at hgen
  have hgen' : gQ = k • Point.vcInvFun γ WP.toAffine gP := eq_of_heq hgen
  refine ⟨γ.map σ, ?_, k, hk, ?_⟩
  · show γ.map σ • WP.map σ = (γ • WP).map σ
    exact WeierstrassCurve.map_variableChange WP γ σ
  · show HEq (WeierstrassCurve.ratPointMap σ (W₀ := γ • WP) gQ)
      (k • Point.vcInvFun (γ.map σ) (WP.map σ).toAffine (WeierstrassCurve.ratPointMap σ (W₀ := WP) gP))
    rw [hgen']
    refine HEq.trans (heq_of_eq (ratPointMap_nsmul σ (γ • WP) k
      (Point.vcInvFun γ WP.toAffine gP))) ?_
    exact Point.heq_nsmul (WeierstrassCurve.map_variableChange WP γ σ).symm k
      (ratPointMap_vcInvFun_heq σ γ WP gP)

def moduliPointMapRingHom (σ : L →+* L') : ModuliPoint N L → ModuliPoint N L' :=
  Quot.lift (fun P => (Quot.mk _ (gamma0PairMap σ P) : ModuliPoint N L'))
    fun _ _ h => Quot.sound (gamma0PairStep_map σ h)

@[simp] theorem moduliPointMapRingHom_mk (σ : L →+* L') (P : Gamma0Pair N L) :
    moduliPointMapRingHom σ (Quot.mk _ P : ModuliPoint N L) =
      (Quot.mk _ (gamma0PairMap σ P) : ModuliPoint N L') := rfl

theorem j_moduliPointMapRingHom (σ : L →+* L') (x : ModuliPoint N L) :
    (moduliPointMapRingHom σ x).j = σ x.j := by
  induction x using Quot.ind with
  | _ P => exact (P.toCurve.map_j σ)

end Map

end ModularCurve

end
