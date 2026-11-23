module

public import Mathlib
public import Theorem.MvPowerSeries.NegV2
public import Structure.MvFormalGroup_CartierModule
public import Def.MvFormalGroup_BasicV2
public import Instance.MvFormalGroup_EndRingV2
public import Theorem.MvPowerSeries.CartierModuleSubst
public import Theorem.MvPowerSeries.CartierModuleInBlk
public import Def.FormalGroup_CartierModule

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup


open MvPowerSeries WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {d d' d'' : ℕ} {R : Type u} [CommRing R]


namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}


@[simp] public theorem toPowerSeries_zero : (0 : CartierModule p Φ).toPowerSeries = fun _ => 0 := rfl


@[simp] public theorem toPowerSeries_add [Φ.IsComm] (f g : CartierModule p Φ) :
    (f + g).toPowerSeries =
      fun j => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries j) := rfl


@[simp] public theorem toPowerSeries_neg [Φ.IsComm] (f : CartierModule p Φ) :
    (-f).toPowerSeries = negSeries Φ f.toPowerSeries := rfl


@[simp] public theorem toPowerSeries_sub [Φ.IsComm] (f g : CartierModule p Φ) :
    (f - g).toPowerSeries =
      fun j => subst (Sum.elim f.toPowerSeries (negSeries Φ g.toPowerSeries)) (Φ.toPowerSeries j) := by
  rw [sub_eq_add_neg]; rfl

end CartierModule

namespace WittLaw

variable (p)


variable {p}

variable (R)


@[simp] public theorem verFam_zero : verFam R 0 = 0 := rfl

omit hp in

@[simp] public theorem verFam_succ (n : ℕ) : verFam R (n + 1) = X n := rfl


variable (p R)


public theorem subst_frobFam (f : MvPowerSeries ℕ R) :
    subst (frobFam p R) f = MvPowerSeries.expand p hp.out.ne_zero f := by
  rw [MvPowerSeries.expand, substAlgHom_apply]
  rfl


end WittLaw

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}


@[simp] public theorem toPowerSeries_precompFun {u : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u)
    (f : CartierModule p Φ) :
    (precompFun hu f).toPowerSeries = fun j => subst u (f.toPowerSeries j) := rfl


@[simp] public theorem toPowerSeries_precomp [Φ.IsComm] {u : ℕ → MvPowerSeries ℕ R}
    (hu : WittLaw.IsEndo p u) (f : CartierModule p Φ) :
    (precomp hu f).toPowerSeries = fun j => subst u (f.toPowerSeries j) := rfl


public theorem precomp_precomp [Φ.IsComm] {u v : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u)
    (hv : WittLaw.IsEndo p v) (f : CartierModule p Φ) (j : Fin d) :
    (precomp hv (precomp hu f)).toPowerSeries j = subst (fun n => subst v (u n)) (f.toPowerSeries j) := by
  show subst v (subst u (f.toPowerSeries j)) = _
  rw [subst_comp_subst_apply hu.hasSubst hv.hasSubst]


@[simp] public theorem toPowerSeries_frobenius [Φ.IsComm] (f : CartierModule p Φ) :
    (frobenius f).toPowerSeries = fun j => subst (WittLaw.verFam R) (f.toPowerSeries j) := rfl


@[simp] public theorem toPowerSeries_verschiebung [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    (verschiebung f).toPowerSeries = fun j => subst (WittLaw.frobFam p R) (f.toPowerSeries j) := rfl


public theorem toPowerSeries_verschiebung_eq_expand [Φ.IsComm] [CharP R p] (f : CartierModule p Φ)
    (j : Fin d) :
    (verschiebung f).toPowerSeries j = MvPowerSeries.expand p hp.out.ne_zero (f.toPowerSeries j) :=
  WittLaw.subst_frobFam _


public theorem frobenius_verschiebung [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    frobenius (verschiebung f) = verschiebung (frobenius f) := by
  apply CartierModule.ext
  funext j
  rw [frobenius, verschiebung, precomp_precomp, precomp_precomp]
  congr 1
  funext n
  cases n with
  | zero =>
    show subst (WittLaw.verFam R) (X 0 ^ p : MvPowerSeries ℕ R) =
      subst (WittLaw.frobFam p R) (0 : MvPowerSeries ℕ R)
    rw [subst_pow WittLaw.hasSubst_verFam, subst_X WittLaw.hasSubst_verFam,
      ← coe_substAlgHom WittLaw.hasSubst_frobFam, map_zero, WittLaw.verFam_zero,
      zero_pow hp.out.ne_zero]
  | succ m =>
    show subst (WittLaw.verFam R) (X (m + 1) ^ p : MvPowerSeries ℕ R) =
      subst (WittLaw.frobFam p R) (X m : MvPowerSeries ℕ R)
    rw [subst_pow WittLaw.hasSubst_verFam, subst_X WittLaw.hasSubst_verFam,
      subst_X WittLaw.hasSubst_frobFam, WittLaw.verFam_succ, WittLaw.frobFam_apply]


public theorem verschiebung_injective [Φ.IsComm] [CharP R p] :
    Function.Injective (verschiebung : CartierModule p Φ → CartierModule p Φ) := by
  intro f g h
  apply CartierModule.ext
  funext j
  ext m
  have hj := congrArg (fun k : CartierModule p Φ => coeff (p • m) (k.toPowerSeries j)) h
  simpa only [toPowerSeries_verschiebung_eq_expand, MvPowerSeries.coeff_expand_smul] using hj


@[simp] public theorem toPowerSeries_mapFun (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    (mapFun φ f).toPowerSeries = fun i => subst f.toPowerSeries (φ.toPowerSeries i) := rfl


@[simp] public theorem toPowerSeries_map [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    (map φ f).toPowerSeries = fun i => subst f.toPowerSeries (φ.toPowerSeries i) := rfl


public theorem map_id [Φ.IsComm] (f : CartierModule p Φ) : map (MvFormalGroup.Hom.id Φ) f = f :=
  CartierModule.ext (funext fun i => subst_X f.hasSubst_toPowerSeries i)


public theorem map_comp [Φ.IsComm] [Φ'.IsComm] [Φ''.IsComm] (ψ : Φ'.Hom Φ'') (φ : Φ.Hom Φ')
    (f : CartierModule p Φ) : map (ψ.comp φ) f = map ψ (map φ f) :=
  CartierModule.ext (funext fun i =>
    subst_comp_subst_apply φ.hasSubst_toPowerSeries f.hasSubst_toPowerSeries (ψ.toPowerSeries i))


public theorem map_add_hom [Φ.IsComm] [Φ'.IsComm] (φ ψ : Φ.Hom Φ') (f : CartierModule p Φ) :
    map (φ + ψ) f = map φ f + map ψ f :=
  CartierModule.ext (funext fun i =>
    subst_subst_elim Φ' φ.constantCoeff_eq_zero ψ.constantCoeff_eq_zero f.hasSubst_toPowerSeries i)


public theorem map_zero_hom [Φ.IsComm] [Φ'.IsComm] (f : CartierModule p Φ) :
    map (0 : Φ.Hom Φ') f = 0 :=
  CartierModule.ext (funext fun i => by
    show subst f.toPowerSeries (0 : MvPowerSeries (Fin d) R) = 0
    rw [← coe_substAlgHom f.hasSubst_toPowerSeries, map_zero])


public theorem map_precomp [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') {u : ℕ → MvPowerSeries ℕ R}
    (hu : WittLaw.IsEndo p u) (f : CartierModule p Φ) :
    map φ (precomp hu f) = precomp hu (map φ f) :=
  CartierModule.ext (funext fun i =>
    (subst_comp_subst_apply f.hasSubst_toPowerSeries hu.hasSubst (φ.toPowerSeries i)).symm)


public theorem map_frobenius [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    map φ (frobenius f) = frobenius (map φ f) :=
  map_precomp φ _ f


public theorem map_verschiebung [Φ.IsComm] [Φ'.IsComm] [CharP R p] (φ : Φ.Hom Φ')
    (f : CartierModule p Φ) : map φ (verschiebung f) = verschiebung (map φ f) :=
  map_precomp φ _ f


@[simp] public theorem endAct_apply [Φ.IsComm] (φ : MvFormalGroup.End Φ) (f : CartierModule p Φ) :
    endAct φ f = map φ f := rfl


public theorem endAct_frobenius [Φ.IsComm] (φ : MvFormalGroup.End Φ) (f : CartierModule p Φ) :
    endAct φ (frobenius f) = frobenius (endAct φ f) :=
  map_frobenius φ f


public theorem endAct_verschiebung [Φ.IsComm] [CharP R p] (φ : MvFormalGroup.End Φ)
    (f : CartierModule p Φ) : endAct φ (verschiebung f) = verschiebung (endAct φ f) :=
  map_verschiebung φ f


public theorem endAct_natCast [Φ.IsComm] (n : ℕ) (f : CartierModule p Φ) :
    endAct (n : MvFormalGroup.End Φ) f = n • f := by
  rw [map_natCast]; rfl

end CartierModule

namespace WittLaw


public theorem constantCoeff_nsmulFam (n k : ℕ) : (nsmulFam p R n k).constantCoeff = 0 := by
  rw [nsmulFam, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
    MvPolynomial.coeff_map, ← MvPolynomial.constantCoeff_eq, MvPolynomial.constantCoeff_rename,
    WittVector.constantCoeff_wittNSMul, map_zero]


public theorem weight_eq_of_coeff_nsmulFam_ne_zero {n k : ℕ} {e : ℕ →₀ ℕ}
    (h : coeff e (nsmulFam p R n k) ≠ 0) : Finsupp.weight (fun m => p ^ m) e = p ^ k := by
  classical
  rw [nsmulFam, MvPolynomial.coeff_coe, MvPolynomial.coeff_map] at h
  have h' : (MvPolynomial.rename Prod.snd (WittVector.wittNSMul p n k)).coeff e ≠ 0 :=
    fun h0 => h (by rw [h0, map_zero])
  obtain ⟨x, hx, hne⟩ := MvPolynomial.coeff_rename_ne_zero _ _ _ h'
  have hw := isWeightedHomogeneous_wittNSMul (p := p) n k hne
  rw [← hx, ← hw, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i c => c • p ^ i) (fun _ => zero_smul ℕ _)
      (fun _ _ _ => add_smul _ _ _)]
  refine Finsupp.sum_congr fun im _ => ?_
  simp [weight]


public theorem hasSubst_nsmulFam (n : ℕ) : HasSubst (nsmulFam p R n) := by
  refine ⟨fun k => by rw [constantCoeff_nsmulFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_lt_nat (Finsupp.weight (fun m => p ^ m) e)).subset fun k hk => ?_
  have hw := weight_eq_of_coeff_nsmulFam_ne_zero (p := p) (R := R) hk
  show k < Finsupp.weight (fun m => p ^ m) e
  rw [hw]
  exact Nat.lt_pow_self hp.out.one_lt

variable (p R) in


public theorem hasSubst_stepFam (n : ℕ) : HasSubst (stepFam p R n) :=
  hasSubst_finCases (hasSubst_nsmulFam n) HasSubst.X


public theorem stepFam_eq (n : ℕ) : stepFam p R n = fun im : Fin 2 × ℕ =>
    ((MvPolynomial.map (Int.castRingHom R) (Fin.cases
      (MvPolynomial.rename Prod.snd (WittVector.wittNSMul p n im.2)) (fun _ => MvPolynomial.X im.2)
        im.1 : MvPolynomial ℕ ℤ) : MvPolynomial ℕ R) : MvPowerSeries ℕ R) := by
  funext ⟨i, m⟩
  refine Fin.cases rfl (fun l => ?_) i
  simp [stepFam]


public theorem nsmulFam_succ (n k : ℕ) :
    nsmulFam p R (n + 1) k = subst (stepFam p R n) (addFam p R k) := by
  have hfun : (fun im : Fin 2 × ℕ => MvPolynomial.rename Prod.snd
      (Fin.cases (WittVector.wittNSMul p n im.2) (fun _ => MvPolynomial.X (0, im.2)) im.1 :
        MvPolynomial (Fin 1 × ℕ) ℤ)) =
      fun im => (Fin.cases (MvPolynomial.rename Prod.snd (WittVector.wittNSMul p n im.2))
        (fun _ => MvPolynomial.X im.2) im.1 : MvPolynomial ℕ ℤ) := by
    funext ⟨i, m⟩
    refine Fin.cases rfl (fun l => ?_) i
    simp
  rw [stepFam_eq, subst_coe_addFam, nsmulFam, ← aeval_wittNSMul_wittAdd,
    MvPolynomial.comp_aeval_apply, hfun]


public theorem nsmulFam_zero (k : ℕ) : nsmulFam p R 0 k = 0 := by
  rw [nsmulFam, wittNSMul_zero, map_zero, map_zero, MvPolynomial.coe_zero]


public theorem nsmulFam_self [CharP R p] (k : ℕ) :
    nsmulFam p R p k = subst (frobFam p R) (verFam R k) := by
  have hcast : Int.castRingHom R = (ZMod.castHom (dvd_refl p) R).comp (Int.castRingHom (ZMod p)) :=
    RingHom.ext_int _ _
  rw [nsmulFam, hcast, ← MvPolynomial.map_map, MvPolynomial.map_rename, map_wittNSMul_self]
  cases k with
  | zero =>
    show ((MvPolynomial.map _ (MvPolynomial.rename Prod.snd (0 : MvPolynomial (Fin 1 × ℕ) (ZMod p))) :
      MvPolynomial ℕ R) : MvPowerSeries ℕ R) = subst (frobFam p R) 0
    rw [map_zero, map_zero, MvPolynomial.coe_zero, ← coe_substAlgHom hasSubst_frobFam, map_zero]
  | succ m =>
    show ((MvPolynomial.map _ (MvPolynomial.rename Prod.snd
        (MvPolynomial.X ((0 : Fin 1), m) ^ p : MvPolynomial (Fin 1 × ℕ) (ZMod p))) :
      MvPolynomial ℕ R) : MvPowerSeries ℕ R) = subst (frobFam p R) (X m)
    rw [map_pow, MvPolynomial.rename_X, map_pow, MvPolynomial.map_X, MvPolynomial.coe_pow,
      MvPolynomial.coe_X, subst_X hasSubst_frobFam]
    rfl

end WittLaw

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}


public theorem subst_nsmulFam [Φ.IsComm] (f : CartierModule p Φ) (n : ℕ) (j : Fin d) :
    subst (WittLaw.nsmulFam p R n) (f.toPowerSeries j) = (n • f).toPowerSeries j := by
  induction n generalizing j with
  | zero =>
    rw [zero_nsmul]
    have h0 : WittLaw.nsmulFam p R 0 = fun _ => 0 := funext WittLaw.nsmulFam_zero
    rw [h0]
    exact subst_zero_of_constantCoeff_eq_zero (f.constantCoeff_eq_zero j)
  | succ n ih =>
    have hf := f.constantCoeff_eq_zero
    have hS := WittLaw.hasSubst_stepFam (p := p) (R := R) n
    have hfam : WittLaw.nsmulFam p R (n + 1) =
        fun k => subst (WittLaw.stepFam p R n) (WittLaw.addFam p R k) :=
      funext (WittLaw.nsmulFam_succ n)
    rw [hfam, ← subst_comp_subst_apply (hasSubst_addFam p R) hS, f.subst_addFam,
      subst_subst_elim Φ (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf) hS, succ_nsmul,
      toPowerSeries_add]
    congr 1
    funext s
    rcases s with l | l
    · show subst (WittLaw.stepFam p R n) (subst (blk 0) (f.toPowerSeries l)) =
        (n • f).toPowerSeries l
      rw [subst_comp_subst_apply (hasSubst_blk 0) hS, ← ih l]
      congr 1
      funext m
      exact subst_X hS ((0 : Fin 2), m)
    · show subst (WittLaw.stepFam p R n) (subst (blk 1) (f.toPowerSeries l)) = f.toPowerSeries l
      rw [subst_comp_subst_apply (hasSubst_blk 1) hS]
      have hX : (fun m => subst (WittLaw.stepFam p R n) (blk (R := R) 1 m)) =
          fun m => (X m : MvPowerSeries ℕ R) := by
        funext m
        exact subst_X hS ((1 : Fin 2), m)
      rw [hX]
      exact congrFun subst_self _


public theorem verschiebung_frobenius [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    verschiebung (frobenius f) = (p : ℕ) • f := by
  apply CartierModule.ext
  funext j
  rw [verschiebung, frobenius, precomp_precomp, ← subst_nsmulFam]
  congr 1
  funext k
  exact (WittLaw.nsmulFam_self k).symm


public theorem frobenius_verschiebung_eq_nsmul [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    frobenius (verschiebung f) = (p : ℕ) • f := by
  rw [frobenius_verschiebung, verschiebung_frobenius]


@[simp] public theorem tangent_apply [Φ.IsComm] (f : CartierModule p Φ) (j : Fin d) :
    tangent f j = coeff (Finsupp.single 0 1) (f.toPowerSeries j) := rfl


public theorem tangent_verschiebung [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    tangent (verschiebung f) = 0 := by
  funext j
  rw [tangent_apply, toPowerSeries_verschiebung_eq_expand]
  exact MvPowerSeries.coeff_expand_of_not_dvd p hp.out.ne_zero _ (i := 0)
    (by simpa using hp.out.one_lt.ne')


public theorem tangent_map [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    tangent (map φ f) = (MvFormalGroup.linearPart φ.toPowerSeries).mulVec (tangent f) := by
  funext i
  show coeff (Finsupp.single 0 1) (subst f.toPowerSeries (φ.toPowerSeries i)) = _
  rw [coeff_single_subst f.constantCoeff_eq_zero, Matrix.mulVec]
  rfl


public theorem constantCoeff_curveFam (n : ℕ) : MvPowerSeries.constantCoeff (curveFam R n) = 0 := by
  cases n with
  | zero => exact MvPowerSeries.constantCoeff_X _
  | succ n => exact map_zero _

omit hp in

public theorem hasSubst_curveFam : HasSubst (curveFam R) := by
  refine ⟨fun n => by rw [constantCoeff_curveFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_singleton 0).subset fun n hn => ?_
  cases n with
  | zero => rfl
  | succ n => exact absurd (by simp [curveFam]) hn


public theorem curve_apply (f : CartierModule p Φ) (j : Fin d) :
    curve f j = subst (curveFam R) (f.toPowerSeries j) := rfl


public theorem constantCoeff_curve (f : CartierModule p Φ) (j : Fin d) :
    PowerSeries.constantCoeff (curve f j) = 0 :=
  constantCoeff_subst_eq_zero hasSubst_curveFam constantCoeff_curveFam (f.constantCoeff_eq_zero j)


public theorem curve_add [Φ.IsComm] (f g : CartierModule p Φ) (j : Fin d) :
    curve (f + g) j = subst (Sum.elim (curve f) (curve g)) (Φ.toPowerSeries j) :=
  subst_subst_elim Φ f.constantCoeff_eq_zero g.constantCoeff_eq_zero hasSubst_curveFam j


public theorem curve_verschiebung [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) (j : Fin d) :
    curve (verschiebung f) j = PowerSeries.expand p hp.out.ne_zero (curve f j) := by
  show subst (curveFam R) (subst (WittLaw.frobFam p R) (f.toPowerSeries j)) =
    MvPowerSeries.expand p hp.out.ne_zero (subst (curveFam R) (f.toPowerSeries j))
  rw [MvPowerSeries.expand, substAlgHom_apply,
    subst_comp_subst_apply WittLaw.hasSubst_frobFam hasSubst_curveFam,
    subst_comp_subst_apply hasSubst_curveFam (HasSubst.X_pow hp.out.ne_zero)]
  congr 1
  funext n
  cases n with
  | zero =>
    show subst (curveFam R) (X 0 ^ p : MvPowerSeries ℕ R) =
      subst (fun s : Unit => (X s : MvPowerSeries Unit R) ^ p) PowerSeries.X
    rw [subst_pow hasSubst_curveFam, subst_X hasSubst_curveFam, PowerSeries.X,
      subst_X (HasSubst.X_pow hp.out.ne_zero)]
    rfl
  | succ m =>
    show subst (curveFam R) (X (m + 1) ^ p : MvPowerSeries ℕ R) =
      subst (fun s : Unit => (X s : MvPowerSeries Unit R) ^ p) (0 : PowerSeries R)
    rw [subst_pow hasSubst_curveFam, subst_X hasSubst_curveFam,
      ← coe_substAlgHom (HasSubst.X_pow hp.out.ne_zero), map_zero]
    exact zero_pow hp.out.ne_zero


public theorem coeff_one_curve [Φ.IsComm] (f : CartierModule p Φ) (j : Fin d) :
    PowerSeries.coeff 1 (curve f j) = tangent f j := by
  classical
  rw [tangent_apply, curve_apply]
  show MvPowerSeries.coeff (Finsupp.single () 1) (subst (curveFam R) (f.toPowerSeries j)) = _
  rw [coeff_subst hasSubst_curveFam]

  have hterm : ∀ e : ℕ →₀ ℕ, e ≠ Finsupp.single 0 1 →
      coeff e (f.toPowerSeries j) •
        coeff (Finsupp.single () 1) (e.prod fun n k => curveFam R n ^ k) = 0 := by
    intro e he
    by_cases hsupp : ∃ n ∈ e.support, n ≠ 0
    · obtain ⟨n, hn, hn0⟩ := hsupp
      have hzero : (e.prod fun n k => curveFam R n ^ k) = 0 := by
        rw [Finsupp.prod]
        refine Finset.prod_eq_zero hn ?_
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        show (0 : PowerSeries R) ^ e (m + 1) = 0
        exact zero_pow (Finsupp.mem_support_iff.mp hn)
      rw [hzero, map_zero, smul_zero]
    · push Not at hsupp
      have he0 : e = Finsupp.single 0 (e 0) := by
        ext n
        by_cases hn : n = 0
        · subst hn; simp
        · rw [Finsupp.single_apply, if_neg (Ne.symm hn)]
          by_contra hne
          exact hn (hsupp n (Finsupp.mem_support_iff.mpr hne))
      have hk : e 0 ≠ 1 := fun h1 => he (by rw [he0, h1])
      rw [he0, Finsupp.prod_single_index (by simp)]
      show coeff _ (f.toPowerSeries j) • coeff (Finsupp.single () 1)
        ((PowerSeries.X : PowerSeries R) ^ e 0) = 0
      rw [PowerSeries.X, coeff_X_pow, if_neg, smul_zero]
      intro h
      exact hk ((Finsupp.single_injective ()) h).symm
  rw [finsum_eq_single _ (Finsupp.single 0 1) hterm, Finsupp.prod_single_index (by simp)]
  show coeff _ (f.toPowerSeries j) • coeff (Finsupp.single () 1)
    ((PowerSeries.X : PowerSeries R) ^ 1) = _
  rw [pow_one, PowerSeries.X, coeff_X, if_pos rfl, smul_eq_mul, mul_one]

namespace Examples


@[simp] public theorem toPowerSeries_addLinear (v : Fin d → R) (i : Fin d) :
    (addLinear p v).toPowerSeries i = v i • (X 0 : MvPowerSeries ℕ R) := rfl


public theorem tangent_addLinear (v : Fin d → R) : tangent (addLinear p v) = v := by
  classical
  funext i
  rw [tangent_apply, toPowerSeries_addLinear, map_smul, coeff_X, if_pos rfl, smul_eq_mul, mul_one]


public theorem tangent_surjective_addMv :
    Function.Surjective (tangent : CartierModule p (addMv d R) → Fin d → R) :=
  fun v => ⟨addLinear p v, tangent_addLinear v⟩


public theorem addLinear_ne_zero [Nontrivial R] {v : Fin d → R} (hv : v ≠ 0) : addLinear p v ≠ 0 := by
  intro h
  apply hv
  have := tangent_addLinear (p := p) v
  rw [h, map_zero] at this
  exact this.symm

end Examples

end CartierModule

end MvFormalGroup

end
