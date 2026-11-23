module

public import Theorem.UpperHalfPlane.XHOperators
public import Theorem.Matrix.IsCuspidalOfType
public import Def.HeckeGalois_EichlerShimura
public import Instance.ModularCurve_FullLevelJacobian
public import Notation.ModularCurve_FullLevelJacobian

public noncomputable section

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace ModularCurve.FullLevel

section Level

variable (q M' : ℕ)

public theorem dvd_sq_mul : q ∣ q ^ 2 * M' :=
  Dvd.dvd.mul_right (dvd_pow_self q two_ne_zero) M'


public theorem mem_levelH_iff (u : (ZMod (q ^ 2 * M'))ˣ) :
    u ∈ levelH q M' ↔ ZMod.unitsMap (dvd_sq_mul q M') u = 1 :=
  MonoidHom.mem_ker


public theorem Idx.ext {ζ ζ' : Idx q} (h : ζ.val = ζ'.val) : ζ = ζ' :=
  Subtype.ext h

variable [Fact q.Prime]


public theorem Idx.isPrimitiveRoot (ζ : Idx q) : IsPrimitiveRoot ζ.val q :=
  (mem_primitiveRoots (Fact.out : q.Prime).pos).1 (ζ : ↥(primitiveRoots q (AlgebraicClosure ℚ))).2


@[simp] public theorem Idx.val_mk (z : AlgebraicClosure ℚ) (hz : IsPrimitiveRoot z q) : (Idx.mk z hz).val = z :=
  rfl


@[simp] public theorem Idx.val_smul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ζ : Idx q) :
    (σ • ζ).val = σ ζ.val :=
  rfl


@[simp] public theorem Idx.val_pow (d : (ZMod q)ˣ) (ζ : Idx q) : (ζ.pow d).val = ζ.val ^ (d : ZMod q).val :=
  rfl

end Idx

section Carrier

variable (q : ℕ) (M' : ℕ)


@[simp] public theorem Jac.eval_mk (f : Idx q → jacComp q M') (ζ : Idx q) : (Jac.mk f).eval ζ = f ζ := rfl


public theorem Jac.ext {x y : Jac q M'} (h : ∀ ζ, x.eval ζ = y.eval ζ) : x = y := funext h


@[simp] public theorem Jac.eval_add (x y : Jac q M') (ζ : Idx q) : (x + y).eval ζ = x.eval ζ + y.eval ζ := rfl

@[simp] public theorem Jac.eval_zero (ζ : Idx q) : (0 : Jac q M').eval ζ = 0 := rfl

@[simp] public theorem Jac.eval_neg (x : Jac q M') (ζ : Idx q) : (-x).eval ζ = -x.eval ζ := rfl

@[simp] public theorem Jac.eval_sub (x y : Jac q M') (ζ : Idx q) : (x - y).eval ζ = x.eval ζ - y.eval ζ := rfl

@[simp] public theorem Jac.eval_zsmul (n : ℤ) (x : Jac q M') (ζ : Idx q) : (n • x).eval ζ = n • x.eval ζ := rfl

@[simp] public theorem Jac.eval_nsmul (n : ℕ) (x : Jac q M') (ζ : Idx q) : (n • x).eval ζ = n • x.eval ζ := rfl


@[simp] public theorem Jac.mapIdx_eval (T : Idx q → (jacComp q M' →+ jacComp q M')) (s : Idx q → Idx q)
    (x : Jac q M') (ζ : Idx q) : (Jac.mapIdx T s x).eval ζ = T ζ (x.eval (s ζ)) := rfl

end Carrier

section Galois

variable (q : ℕ) [Fact q.Prime] (M' : ℕ)

open scoped ModularCurve_FullLevelJacobian


public theorem galJac_eval (σ : Gal) (x : Jac q M') (ζ : Idx q) :
    (galJac q M' σ x).eval ζ = σ • x.eval (σ⁻¹ • ζ) :=
  rfl

end Galois

section LevelAut

variable (q : ℕ) [Fact q.Prime] (M' : ℕ)


public theorem isLevelAutBar_levelAutBar {ζ : Idx q} {γ : SL(2, ℤ)}
    (h : ∃ τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M', IsLevelAutBar q M' ζ γ τ) :
    IsLevelAutBar q M' ζ γ (levelAutBar q M' ζ γ) := by
  rw [levelAutBar, dif_pos h]
  exact h.choose_spec


public theorem levelAutBar_of_not {ζ : Idx q} {γ : SL(2, ℤ)}
    (h : ¬ ∃ τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M', IsLevelAutBar q M' ζ γ τ) :
    levelAutBar q M' ζ γ = AlgEquiv.refl := by
  rw [levelAutBar, dif_neg h]

variable (q M')


public theorem levelOp_apply (ζ : Idx q) (γ : SL(2, ℤ)) (x : jacComp q M') :
    levelOp q M' ζ γ x = SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ) • x :=
  rfl

variable {q M'} in


public theorem levelOp_of_not {ζ : Idx q} {γ : SL(2, ℤ)}
    (h : ¬ ∃ τ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M', IsLevelAutBar q M' ζ γ τ)
    (x : jacComp q M') : levelOp q M' ζ γ x = x := by
  rw [levelOp_apply, levelAutBar_of_not h]
  have : SemilinearAut.ofAlgAut
      (AlgEquiv.refl : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M') = 1 :=
    map_one _
  rw [this, one_smul]


@[simp] public theorem coe_diagOneElem (d : (ZMod q)ˣ) :
    ((diagOneElem q d : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![1, 0; 0, (d : ZMod q)] :=
  rfl


@[simp] public theorem slJac_eval (γ : SL(2, ℤ)) (x : Jac q M') (ζ : Idx q) :
    (slJac q M' γ x).eval ζ = levelOp q M' ζ γ⁻¹ (x.eval ζ) :=
  rfl


@[simp] public theorem diagJac_eval (d : (ZMod q)ˣ) (x : Jac q M') (ζ : Idx q) :
    (diagJac q M' d x).eval ζ = x.eval (ζ.pow d⁻¹) :=
  rfl


public theorem gl2Jac_redQ (h : GL2Laws q M') (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    gl2Jac q M' (redQ q γ) = slJac q M' γ := by
  rw [gl2Jac, dif_pos h]
  exact h.choose_spec.1 γ hγ


public theorem gl2Jac_diagOneElem (h : GL2Laws q M') (d : (ZMod q)ˣ) :
    gl2Jac q M' (diagOneElem q d) = diagJac q M' d := by
  rw [gl2Jac, dif_pos h]
  exact h.choose_spec.2 d


public theorem gl2Jac_of_not (h : ¬ GL2Laws q M') : gl2Jac q M' = 1 := by
  rw [gl2Jac, dif_neg h]

variable (q M')


public theorem heckeGenJac_of_dvd {ℓ : ℕ} (h : ℓ ∣ q * M') : heckeGenJac q M' ℓ = 0 := by
  rw [heckeGenJac, dif_neg (fun h' => h'.2 h)]


public theorem heckeGenJac_of_not_prime {ℓ : ℕ} (h : ¬ ℓ.Prime) : heckeGenJac q M' ℓ = 0 := by
  rw [heckeGenJac, dif_neg (fun h' => h h'.1)]


public theorem heckeGenJac_eval {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓqM : ¬ ℓ ∣ q * M') (hq : ℓ.Coprime q)
    (hqM : ℓ.Coprime (q ^ 2 * M')) (x : Jac q M') (ζ : Idx q) :
    (heckeGenJac q M' ℓ x).eval ζ =
      diamondHBar (q ^ 2 * M') (levelH q M') (ZMod.unitOfCoprime ℓ hqM)⁻¹
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
          heckeOperatorHAlong (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M') ℓ
            (x.eval (ζ.pow (ZMod.unitOfCoprime ℓ hq)⁻¹))) := by
  rw [heckeGenJac, dif_pos ⟨hℓ, hℓqM⟩]
  rfl

variable (q M')


public theorem isMulCommutative_adjoin_heckeGenJac (h : HeckeGenCommute q M') :
    IsMulCommutative (Algebra.adjoin ℤ (Set.range fun ℓ : Nat.Primes => heckeGenJac q M' ℓ)) :=
  Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨ℓ, rfl⟩ _ ⟨ℓ', rfl⟩
    exact h ℓ ℓ')

open scoped IsMulCommutative in


public theorem heckeJacAux_heckeGen (h : HeckeGenCommute q M') (ℓ : Nat.Primes) :
    (heckeJacAux h (heckeGen ℓ) : AddMonoid.End (Jac q M')) = heckeGenJac q M' ℓ := by
  haveI := isMulCommutative_adjoin_heckeGenJac h
  rw [heckeJacAux, heckeGen, MvPolynomial.aeval_X]

variable (q M')


public theorem heckeJac_heckeGen (h : HeckeGenCommute q M') (ℓ : Nat.Primes) :
    heckeJac q M' (heckeGen ℓ) = heckeGenJac q M' ℓ := by
  rw [heckeJac, dif_pos h]
  exact heckeJacAux_heckeGen h ℓ


public theorem heckeJac_heckeGen_of_not (h : ¬ HeckeGenCommute q M') (ℓ : Nat.Primes) :
    heckeJac q M' (heckeGen ℓ) = 0 := by
  rw [heckeJac, dif_neg h, heckeGen, RingHom.comp_apply, MvPolynomial.eval₂Hom_zero_apply,
    MvPolynomial.constantCoeff_X, map_zero, map_zero]


public theorem heckeJac_heckeGen_of_dvd (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ∣ q * M') :
    heckeJac q M' (heckeGen ℓ) = 0 := by
  by_cases h : HeckeGenCommute q M'
  · rw [heckeJac_heckeGen h, heckeGenJac_of_dvd hℓ]
  · exact heckeJac_heckeGen_of_not h ℓ

end Operators

section Tate

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) (lam : ℕ) [Fact lam.Prime]

open scoped ModularCurve_FullLevelJacobian

example : DistribMulAction (AddMonoid.End (Jac q M')) (Jac q M') := inferInstance


public theorem tateEnd_apply_coe (f : AddMonoid.End (Jac q M')) (x : TateModule lam (Jac q M')) (n : ℕ) :
    ((tateEnd q M' lam f x : TateModule lam (Jac q M')) : ℕ → Jac q M') n = f ((x : ℕ → Jac q M') n) :=
  rfl


public theorem tateGal_apply_coe (σ : Gal) (x : TateModule lam (Jac q M')) (n : ℕ) :
    ((tateGal q M' lam σ x : TateModule lam (Jac q M')) : ℕ → Jac q M') n = galJac q M' σ ((x : ℕ → Jac q M') n) :=
  rfl


public theorem tateHecke_apply_coe (t : HeckeAlg) (x : TateModule lam (Jac q M')) (n : ℕ) :
    ((tateHecke q M' lam t x : TateModule lam (Jac q M')) : ℕ → Jac q M') n = heckeJac q M' t ((x : ℕ → Jac q M') n) :=
  rfl


public theorem tateGL2_apply_coe (g : CuspidalType.GL2 q) (x : TateModule lam (Jac q M')) (n : ℕ) :
    ((tateGL2 q M' lam g x : TateModule lam (Jac q M')) : ℕ → Jac q M') n = gl2Jac q M' g ((x : ℕ → Jac q M') n) :=
  rfl


public theorem tateHecke_heckeGen_of_dvd (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ∣ q * M') :
    tateHecke q M' lam (heckeGen ℓ) = 0 := by
  rw [tateHecke, RingHom.comp_apply, heckeJac_heckeGen_of_dvd ℓ hℓ, map_zero]

end Tate

end ModularCurve.FullLevel

end
