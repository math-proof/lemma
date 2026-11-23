module

public import Mathlib
public import Def.M4aHerbrand_IdeleClassVocab
public import Theorem.Set.FiniteUnitIdelesOutside

public noncomputable section

set_option autoImplicit false

open NumberField IsDedekindDomain CategoryTheory Set

noncomputable section

namespace M4aHerbrand

section comm

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

end comm

section Carrier

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]


@[simp] public theorem coe_infPart_apply (x : (AdeleRing R F)ˣ) : (infPart x : InfiniteAdeleRing F) = (x : AdeleRing R F).1 := rfl


@[simp] public theorem coe_finPart_apply (w : HeightOneSpectrum R) (x : (AdeleRing R F)ˣ) :
    (finPart w x : w.adicCompletion F) = (x : AdeleRing R F).2 w := rfl

variable (R F)


public theorem mem_idelesTrivialOn_iff (T : Set (HeightOneSpectrum R)) (x : (AdeleRing R F)ˣ) :
    x ∈ idelesTrivialOn R F T ↔ infPart x = 1 ∧ ∀ w ∈ T, finPart w x = 1 := Iff.rfl


public theorem idelesTrivialOn_antitone : Antitone (idelesTrivialOn R F) :=
  fun _ _ h _ hx => ⟨hx.1, fun w hw => hx.2 w (h hw)⟩


public theorem unitIdelesTrivialOn_le_unitIdelesOutside (T : Set (HeightOneSpectrum R)) :
    unitIdelesTrivialOn R F T ≤ NumberField.AdeleRing.unitIdelesOutside R F T := inf_le_left


public theorem unitIdelesTrivialOn_le_idelesTrivialOn (T : Set (HeightOneSpectrum R)) :
    unitIdelesTrivialOn R F T ≤ idelesTrivialOn R F T := inf_le_right

variable {R F}


public theorem mem_unitIdelesTrivialOn_iff (T : Set (HeightOneSpectrum R)) (x : (AdeleRing R F)ˣ) :
    x ∈ unitIdelesTrivialOn R F T ↔
      (∀ w : HeightOneSpectrum R, w ∉ T → (x : AdeleRing R F).2 w ∈ w.adicCompletionIntegers F ∧
        ((x⁻¹ : (AdeleRing R F)ˣ) : AdeleRing R F).2 w ∈ w.adicCompletionIntegers F) ∧
      infPart x = 1 ∧ ∀ w ∈ T, finPart w x = 1 := Iff.rfl


public theorem unitIdelesTrivialOn_antitone : Antitone (unitIdelesTrivialOn R F) := by
  intro T T' hTT' x hx
  refine ⟨fun w hw => ?_, idelesTrivialOn_antitone R F hTT' hx.2⟩
  by_cases hw' : w ∈ T'
  · have h1 : (x : AdeleRing R F).2 w = 1 := congrArg Units.val (hx.2.2 w hw')
    have h2 : ((x⁻¹ : (AdeleRing R F)ˣ) : AdeleRing R F).2 w = 1 :=
      congrArg Units.val (show finPart w x⁻¹ = 1 by rw [map_inv, hx.2.2 w hw', inv_one])
    exact ⟨h1 ▸ one_mem _, h2 ▸ one_mem _⟩
  · exact hx.1 w hw'


public theorem unitIdelesTrivialOn_univ : unitIdelesTrivialOn R F Set.univ = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have h1 : (x : AdeleRing R F).1 = 1 := congrArg Units.val hx.2.1
  have h2 : ∀ w, (x : AdeleRing R F).2 w = 1 := fun w => congrArg Units.val (hx.2.2 w (Set.mem_univ w))
  exact Units.ext (Prod.ext h1 (DFunLike.ext _ _ h2))

end Carrier

section SClass

variable (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]


public theorem principalIdeles_le_sClassKernel (T : Set (HeightOneSpectrum R)) : principalIdeles R F ≤ sClassKernel R F T := le_sup_left


public theorem unitIdelesTrivialOn_le_sClassKernel (T : Set (HeightOneSpectrum R)) : unitIdelesTrivialOn R F T ≤ sClassKernel R F T :=
  le_sup_right


public theorem sClassKernel_antitone : Antitone (sClassKernel R F) :=
  fun _ _ h => sup_le_sup_left (unitIdelesTrivialOn_antitone h) _


public theorem sClassKernel_univ : sClassKernel R F Set.univ = principalIdeles R F := by
  rw [sClassKernel, unitIdelesTrivialOn_univ, sup_bot_eq]


@[simp] public theorem toSIdeleClass_mk (T : Set (HeightOneSpectrum R)) (x : (AdeleRing R F)ˣ) :
    toSIdeleClass R F T (QuotientGroup.mk x) = QuotientGroup.mk x := rfl


public theorem toSIdeleClass_surjective (T : Set (HeightOneSpectrum R)) : Function.Surjective (toSIdeleClass R F T) :=
  fun c => by obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c; exact ⟨QuotientGroup.mk x, toSIdeleClass_mk R F T x⟩


public theorem toSIdeleClass_mk_eq_one_iff (T : Set (HeightOneSpectrum R)) (x : (AdeleRing R F)ˣ) :
    toSIdeleClass R F T (QuotientGroup.mk x) = 1 ↔ x ∈ sClassKernel R F T :=
  QuotientGroup.eq_one_iff x


public theorem ker_toSIdeleClass (T : Set (HeightOneSpectrum R)) : (toSIdeleClass R F T).ker = sUnitClasses R F T := by
  rw [toSIdeleClass, QuotientGroup.ker_map, Subgroup.comap_id, sClassKernel, Subgroup.map_sup,
    QuotientGroup.map_mk'_self, bot_sup_eq, sUnitClasses]


public theorem sUnitClasses_antitone : Antitone (sUnitClasses R F) :=
  fun _ _ h => Subgroup.map_mono (unitIdelesTrivialOn_antitone h)


public theorem sUnitClasses_univ : sUnitClasses R F Set.univ = ⊥ := by
  rw [sUnitClasses, unitIdelesTrivialOn_univ, Subgroup.map_bot]

namespace SIdeleClassGroup

variable {R F}


@[simp] public theorem ofLE_mk {T T' : Set (HeightOneSpectrum R)} (h : T ⊆ T') (x : (AdeleRing R F)ˣ) :
    ofLE h (QuotientGroup.mk x : SIdeleClassGroup R F T') = QuotientGroup.mk x := rfl


@[simp] public theorem ofLE_toSIdeleClass {T T' : Set (HeightOneSpectrum R)} (h : T ⊆ T') (c : IdeleClassGroup R F) :
    ofLE h (toSIdeleClass R F T' c) = toSIdeleClass R F T c := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c; rfl


public theorem ofLE_surjective {T T' : Set (HeightOneSpectrum R)} (h : T ⊆ T') : Function.Surjective (ofLE (R := R) (F := F) h) :=
  fun c => by obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c; exact ⟨QuotientGroup.mk x, ofLE_mk h x⟩


public theorem ofLE_refl (T : Set (HeightOneSpectrum R)) : ofLE (subset_refl T) = MonoidHom.id (SIdeleClassGroup R F T) :=
  QuotientGroup.map_id _


public theorem ofLE_comp_ofLE {T T' T'' : Set (HeightOneSpectrum R)} (h : T ⊆ T') (h' : T' ⊆ T'') :
    (ofLE h).comp (ofLE (R := R) (F := F) h') = ofLE (h.trans h') :=
  MonoidHom.ext fun c => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    simp only [MonoidHom.comp_apply, ofLE_mk]

end SIdeleClassGroup

end SClass

section Descent

variable {R E F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]

namespace IdeleGaloisDescent


@[simp] public theorem classAct_mk (D : IdeleGaloisDescent R E F) (g : F ≃ₐ[E] F) (x : (AdeleRing R F)ˣ) :
    D.classAct g (QuotientGroup.mk x) = QuotientGroup.mk (D.unitsAct g x) := rfl


public theorem classAct_one (D : IdeleGaloisDescent R E F) (c : IdeleClassGroup R F) : D.classAct 1 c = c := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  rw [classAct_mk, map_one]; rfl


public theorem classAct_mul (D : IdeleGaloisDescent R E F) (g h : F ≃ₐ[E] F) (c : IdeleClassGroup R F) :
    D.classAct (g * h) c = D.classAct g (D.classAct h c) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  rw [classAct_mk, classAct_mk, classAct_mk, map_mul]; rfl


public theorem classMulDistribMulAction_smul (D : IdeleGaloisDescent R E F) (g : F ≃ₐ[E] F) (c : IdeleClassGroup R F) :
    (letI := D.classMulDistribMulAction; g • c) = D.classAct g c := rfl


public theorem sClassKernel_le_comap_unitsAct (D : IdeleGaloisDescent R E F) (hD : D.StabilizesUnitIdeles T) (g : F ≃ₐ[E] F) :
    sClassKernel R F T ≤ (sClassKernel R F T).comap (D.unitsAct g).toMonoidHom := by
  refine sup_le ?_ fun x hx => unitIdelesTrivialOn_le_sClassKernel R F T (hD g x hx)
  rw [← Subgroup.map_le_iff_le_comap, D.map_principalIdeles g]
  exact principalIdeles_le_sClassKernel R F T


@[simp] public theorem sClassAct_mk (D : IdeleGaloisDescent R E F) (hD : D.StabilizesUnitIdeles T) (g : F ≃ₐ[E] F)
    (x : (AdeleRing R F)ˣ) : D.sClassAct hD g (QuotientGroup.mk x) = QuotientGroup.mk (D.unitsAct g x) := rfl


@[simp] public theorem sClassAct_toSIdeleClass (D : IdeleGaloisDescent R E F) (hD : D.StabilizesUnitIdeles T) (g : F ≃ₐ[E] F)
    (c : IdeleClassGroup R F) : D.sClassAct hD g (toSIdeleClass R F T c) = toSIdeleClass R F T (D.classAct g c) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c; rfl


public theorem sClassAct_one (D : IdeleGaloisDescent R E F) (hD : D.StabilizesUnitIdeles T) (c : SIdeleClassGroup R F T) :
    D.sClassAct hD 1 c = c := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  rw [sClassAct_mk, map_one]; rfl


public theorem sClassAct_mul (D : IdeleGaloisDescent R E F) (hD : D.StabilizesUnitIdeles T) (g h : F ≃ₐ[E] F)
    (c : SIdeleClassGroup R F T) : D.sClassAct hD (g * h) c = D.sClassAct hD g (D.sClassAct hD h c) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  rw [sClassAct_mk, sClassAct_mk, sClassAct_mk, map_mul]; rfl


public theorem sClassMulDistribMulAction_smul_toSIdeleClass (D : IdeleGaloisDescent R E F) (hD : D.StabilizesUnitIdeles T)
    (g : F ≃ₐ[E] F) (c : IdeleClassGroup R F) :
    (letI := D.sClassMulDistribMulAction hD; g • toSIdeleClass R F T c) = toSIdeleClass R F T (D.classAct g c) :=
  D.sClassAct_toSIdeleClass hD g c

end IdeleGaloisDescent

end Descent

section RepHoms

universe u

variable {G : Type u} [Group G] {M N : Type u} [CommGroup M] [CommGroup N]
  [MulDistribMulAction G M] [MulDistribMulAction G N]


@[simp] public theorem repHomOfMulEquivariant_hom_apply (f : M →* N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (x : Additive M) : (repHomOfMulEquivariant f hf).hom x = Additive.ofMul (f (Additive.toMul x)) := rfl

variable {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
variable {Γ : Type} [Group Γ]


public theorem toSIdeleClass_smul_of_descent {E : Type} [Field E] [Algebra E F] (D : IdeleGaloisDescent R E F)
    (T : Set (HeightOneSpectrum R)) [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup R F)]
    [MulDistribMulAction (F ≃ₐ[E] F) (SIdeleClassGroup R F T)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup R F), g • c = D.classAct g c)
    (hactS : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup R F), g • toSIdeleClass R F T c = toSIdeleClass R F T (D.classAct g c))
    (g : F ≃ₐ[E] F) (c : IdeleClassGroup R F) : toSIdeleClass R F T (g • c) = g • toSIdeleClass R F T c := by
  rw [hact, hactS]


public theorem SIdeleClassGroup.ofLE_smul_of_descent {E : Type} [Field E] [Algebra E F] (D : IdeleGaloisDescent R E F)
    {T T' : Set (HeightOneSpectrum R)} (hTT' : T ⊆ T')
    [MulDistribMulAction (F ≃ₐ[E] F) (SIdeleClassGroup R F T')] [MulDistribMulAction (F ≃ₐ[E] F) (SIdeleClassGroup R F T)]
    (hactS' : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup R F), g • toSIdeleClass R F T' c = toSIdeleClass R F T' (D.classAct g c))
    (hactS : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup R F), g • toSIdeleClass R F T c = toSIdeleClass R F T (D.classAct g c))
    (g : F ≃ₐ[E] F) (c : SIdeleClassGroup R F T') :
    SIdeleClassGroup.ofLE hTT' (g • c) = g • SIdeleClassGroup.ofLE hTT' c := by
  obtain ⟨c, rfl⟩ := toSIdeleClass_surjective R F T' c
  rw [hactS', SIdeleClassGroup.ofLE_toSIdeleClass, SIdeleClassGroup.ofLE_toSIdeleClass, hactS]

end RepHoms

end M4aHerbrand

namespace NumberField

variable (E F : Type*) [Field E] [Field F] [Algebra E F]


public theorem placesOver_mono {S S' : Set (HeightOneSpectrum (𝓞 E))} (h : S ⊆ S') : placesOver E F S ⊆ placesOver E F S' :=
  fun _ ⟨v, hv, hw⟩ => ⟨v, h hv, hw⟩


public theorem mem_placesOver_iff (S : Set (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 F)) :
    w ∈ placesOver E F S ↔ ∃ v ∈ S, w.asIdeal.under (𝓞 E) = v.asIdeal := Iff.rfl


public theorem placesOverPrimes_mono {S S' : Set Nat.Primes} (h : S ⊆ S') : placesOverPrimes F S ⊆ placesOverPrimes F S' :=
  fun _ ⟨p, hp, hw⟩ => ⟨p, h hp, hw⟩


public theorem mem_placesOverPrimes_iff (S : Set Nat.Primes) (w : HeightOneSpectrum (𝓞 F)) :
    w ∈ placesOverPrimes F S ↔ ∃ p ∈ S, ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := Iff.rfl

end NumberField

end
