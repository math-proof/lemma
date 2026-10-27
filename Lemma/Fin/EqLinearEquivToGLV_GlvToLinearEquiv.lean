import Mathlib
import Initialize.Tactic.Attr.Basic
import Class.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics.Part3
open GeometricAlgebra GeometricAlgebra.Flag


/--
[linearEquivToGLV_glvToLinearEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
@[path]
private lemma main
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {g : GLV k V} :
-- imply
  linearEquivToGLV (glvToLinearEquiv g) = g := by
-- proof
  ext x; show (glvToLinearEquiv g).toLinearMap x = (↑g : V →ₗ[k] V) x
  rw [glvToLinearEquiv_toLinearMap]



/--
[linearEquivToGLV_mul_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma linearEquivToGLV_mul_val
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {d u : V ≃ₗ[k] V} :
-- imply
  (↑(linearEquivToGLV d * linearEquivToGLV u) : V →ₗ[k] V) = d.toLinearMap.comp u.toLinearMap := by
-- proof
  show (↑(linearEquivToGLV d) : V →ₗ[k] V) ∘ₗ (↑(linearEquivToGLV u) : V →ₗ[k] V) = _; simp



/--
[parabolic_mem_preserves](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma parabolic_mem_preserves
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {F : Flag k V}
  {g : GLV k V}
  {i : Fin F.len}
  {v : V}
-- given
  (hg : g ∈ F.parabolicSubgroup)
  (hv : v ∈ F.spaces i) :
-- imply
  (↑g : V →ₗ[k] V) v ∈ F.spaces i := by
-- proof
  rw [← hg i]; exact Submodule.mem_map_of_mem hv



/--
[gl_mul_inv_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma gl_mul_inv_cancel
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {g : GLV k V}
  {v : V} :
-- imply
  (↑g : V →ₗ[k] V) ((↑(g⁻¹) : V →ₗ[k] V) v) = v := by
-- proof
  change ((↑g : V →ₗ[k] V) ∘ₗ (↑(g⁻¹) : V →ₗ[k] V)) v = v
  have : (↑g : V →ₗ[k] V) ∘ₗ (↑(g⁻¹) : V →ₗ[k] V) = LinearMap.id := by
    ext x; change (↑(g * g⁻¹) : V →ₗ[k] V) x = x; simp [mul_inv_cancel]
  rw [this]; simp



/--
[gl_conj_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma gl_conj_apply
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {g u : GLV k V}
  {v : V} :
-- imply
  (↑(g * u * g⁻¹) : V →ₗ[k] V) v = (↑g : V →ₗ[k] V) ((↑u : V →ₗ[k] V) ((↑(g⁻¹) : V →ₗ[k] V) v)) := by
-- proof
  simp [Units.val_mul]



/--
[conj_minus_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma conj_minus_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {g u : GLV k V}
  {v : V} :
-- imply
  (↑(g * u * g⁻¹) : V →ₗ[k] V) v - v = (↑g : V →ₗ[k] V) ((↑u : V →ₗ[k] V) ((↑(g⁻¹) : V →ₗ[k] V) v) - (↑(g⁻¹) : V →ₗ[k] V) v) := by
-- proof
  rw [gl_conj_apply, map_sub]; congr 1; exact (gl_mul_inv_cancel g v).symm



/--
[parabolic_conj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma parabolic_conj
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {F₁ F₂ : Flag k V}
  {g : GLV k V}
-- given
  (hlen : F₁.len = F₂.len)
  (hg : ∀ i : Fin F₁.len, (F₁.spaces i).map (↑g : V →ₗ[k] V) = F₂.spaces (i.cast hlen)) :
-- imply
  F₂.parabolicSubgroup = (F₁.parabolicSubgroup).map (MulAut.conj g).toMonoidHom := by
-- proof
  ext h
  simp only [Subgroup.mem_map]
  constructor
  ·
    intro hh
    refine ⟨g⁻¹ * h * g, ?_, ?_⟩
    ·
      intro i
      rw [show (g⁻¹ * h * g : GLV k V) = g⁻¹ * (h * g) from by group]
      rw [submodule_map_mul_eq, submodule_map_mul_eq]
      rw [hg i, hh (i.cast hlen), map_inv_of_map_to g _ _ (hg i)]
    ·
      simp [MulAut.conj_apply]; group
  ·
    rintro ⟨p, hp, rfl⟩
    intro j
    have hval : (↑((MulEquiv.toMonoidHom (MulAut.conj g)) p) : V →ₗ[k] V) =
      (↑(g * p * g⁻¹) : V →ₗ[k] V) := by simp [MulAut.conj_apply]
    show (F₂.spaces j).map (↑((MulEquiv.toMonoidHom (MulAut.conj g)) p) : V →ₗ[k] V) = F₂.spaces j
    rw [hval, show (g * p * g⁻¹ : GLV k V) = g * (p * g⁻¹) from by group]
    rw [submodule_map_mul_eq, submodule_map_mul_eq]
    let i : Fin F₁.len := j.cast hlen.symm
    rw [show j = i.cast hlen from by simp [i]]
    rw [map_inv_of_map_to g _ _ (hg i), hp i, hg i]



/--
[inf_map_conj_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma inf_map_conj_of_mem
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [Group G]
  {H K : Subgroup G}
  {g : G}
-- given
  (hg : g ∈ H) :
-- imply
  (H ⊓ K).map (MulAut.conj g).toMonoidHom = H ⊓ K.map (MulAut.conj g).toMonoidHom := by
-- proof
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨y, ⟨hyH, hyK⟩, rfl⟩
    exact ⟨H.mul_mem (H.mul_mem hg hyH) (H.inv_mem hg), y, hyK, rfl⟩
  · rintro ⟨hxH, y, hyK, rfl⟩
    refine ⟨y, ⟨?_, hyK⟩, rfl⟩
    have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem hg) hxH) hg



/--
[conj_map_inf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma conj_map_inf
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {H K : Subgroup (GLV k V)}
  {g : GLV k V} :
-- imply
  (H ⊓ K).map (MulAut.conj g).toMonoidHom = H.map (MulAut.conj g).toMonoidHom ⊓ K.map (MulAut.conj g).toMonoidHom :=
-- proof
  Subgroup.map_inf_eq H K _ (MulEquiv.injective _)



/--
[FlagsOfSameTypeAreGLEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma FlagsOfSameTypeAreGLEquivalent
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [FlagEquivalenceProperty k V] :
-- imply
  ∀ F₁ F₂ : Flag k V, F₁.sameType F₂ → ∃ (g : GLV k V) (hlen : F₁.len = F₂.len), ∀ i : Fin F₁.len, (F₁.spaces i).map (↑g : V →ₗ[k] V) = F₂.spaces (i.cast hlen) := by
-- proof
  intro F₁ F₂ hst
  obtain ⟨e, hlen, he⟩ := FlagEquivalenceProperty.equiv_linear F₁ F₂ hst
  refine ⟨linearEquivToGLV e, hlen, fun i => ?_⟩
  rw [linearEquivToGLV_val]
  exact he i



/--
[OppositeSystemsAreConjugate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma OppositeSystemsAreConjugate
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [OppositeSystemsConjugacyProperty k V] :
-- imply
  ∀ (F : Flag k V) (F'₁ F'₂ : Flag k V) (_h₁ : Flag.isOppositeFlag F F'₁) (_h₂ : Flag.isOppositeFlag F F'₂), ∃ (p : GLV k V) (_hp : p ∈ F.parabolicSubgroup) (hlen : F'₁.len = F'₂.len), ∀ i : Fin F'₁.len, (F'₁.spaces i).map (↑p : V →ₗ[k] V) = F'₂.spaces (i.cast hlen) := by
-- proof
  intro F F'₁ F'₂ h₁ h₂
  obtain ⟨e, hlen, hpres, hmap⟩ :=
    OppositeSystemsConjugacyProperty.conjugate_linear F F'₁ F'₂ h₁ h₂
  refine ⟨linearEquivToGLV e, ?_, hlen, fun i => ?_⟩
  ·
    intro i
    rw [linearEquivToGLV_val]
    exact hpres i
  · rw [linearEquivToGLV_val]
    exact hmap i



/--
[SemidirectDecompositionExists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma SemidirectDecompositionExists
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [SemidirectDecompositionProperty k V] :
-- imply
  ∀ (F F' : Flag k V) (h : Flag.isOppositeFlag F F') (hlen : 0 < F.len) (_hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤) (p : GLV k V), p ∈ F.parabolicSubgroup → ∃ m u : GLV k V, m ∈ Flag.leviComponent F F' h ∧ u ∈ F.unipotentRadical ∧ p = m * u := by
-- proof
  intro F F' hopp hlen hcov p hp
  let pe := glvToLinearEquiv p
  have hpe : ∀ i : Fin F.len, (F.spaces i).map pe.toLinearMap = F.spaces i :=
    fun i => by simp [pe]; exact hp i
  obtain ⟨d, u, hd_F, hd_F', hu_F, hu_unip, hcomp⟩ :=
    SemidirectDecompositionProperty.exists_decomp_linear F F' hopp hlen hcov pe hpe
  refine ⟨linearEquivToGLV d, linearEquivToGLV u, ?_, ?_, ?_⟩
  ·
    exact ⟨fun i => by rw [linearEquivToGLV_val]; exact hd_F i,
      fun i => by rw [linearEquivToGLV_val]; exact hd_F' i⟩
  ·
    refine ⟨fun i => by rw [linearEquivToGLV_val]; exact hu_F i, ?_⟩
    intro i v hv
    show (↑(linearEquivToGLV u) : V →ₗ[k] V) v - v ∈ _
    rw [linearEquivToGLV_val]
    exact hu_unip i v hv
  ·
    ext x
    have : (↑p : V →ₗ[k] V) x = (d.toLinearMap.comp u.toLinearMap) x := by
      rw [← hcomp]; simp [pe]
    rw [this]
    show _ = (↑(linearEquivToGLV d * linearEquivToGLV u) : V →ₗ[k] V) x
    rw [linearEquivToGLV_mul_val]



/--
[SemidirectDecompositionUnique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma SemidirectDecompositionUnique
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [SemidirectDecompositionProperty k V] :
-- imply
  ∀ (F F' : Flag k V) (h : Flag.isOppositeFlag F F') (hlen : 0 < F.len) (_hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤) (m₁ m₂ u₁ u₂ : GLV k V), m₁ ∈ Flag.leviComponent F F' h → m₂ ∈ Flag.leviComponent F F' h → u₁ ∈ F.unipotentRadical → u₂ ∈ F.unipotentRadical → m₁ * u₁ = m₂ * u₂ → m₁ = m₂ ∧ u₁ = u₂ := by
-- proof
  intro F F' hopp hlen hcov m₁ m₂ u₁ u₂ hm₁ hm₂ hu₁ hu₂ heq
  let d₁ := glvToLinearEquiv m₁
  let d₂ := glvToLinearEquiv m₂
  let e₁ := glvToLinearEquiv u₁
  let e₂ := glvToLinearEquiv u₂
  have hd₁_F : ∀ i : Fin F.len, (F.spaces i).map d₁.toLinearMap = F.spaces i :=
    fun i => by simp [d₁]; exact hm₁.1 i
  have hd₁_F' : ∀ i : Fin F'.len, (F'.spaces i).map d₁.toLinearMap = F'.spaces i :=
    fun i => by simp [d₁]; exact hm₁.2 i
  have hd₂_F : ∀ i : Fin F.len, (F.spaces i).map d₂.toLinearMap = F.spaces i :=
    fun i => by simp [d₂]; exact hm₂.1 i
  have hd₂_F' : ∀ i : Fin F'.len, (F'.spaces i).map d₂.toLinearMap = F'.spaces i :=
    fun i => by simp [d₂]; exact hm₂.2 i
  have he₁_F : ∀ i : Fin F.len, (F.spaces i).map e₁.toLinearMap = F.spaces i :=
    fun i => by simp [e₁]; exact hu₁.1 i
  have he₁_unip : ∀ i : Fin F.len, ∀ v ∈ F.spaces i,
    e₁.toLinearMap v - v ∈
      if h : (i : ℕ) = 0 then (⊥ : Submodule k V)
      else F.spaces ⟨i.val - 1, by omega⟩ :=
    fun i v hv => by simp only [e₁, glvToLinearEquiv_toLinearMap]; exact hu₁.2 i v hv
  have he₂_F : ∀ i : Fin F.len, (F.spaces i).map e₂.toLinearMap = F.spaces i :=
    fun i => by simp [e₂]; exact hu₂.1 i
  have he₂_unip : ∀ i : Fin F.len, ∀ v ∈ F.spaces i,
    e₂.toLinearMap v - v ∈
      if h : (i : ℕ) = 0 then (⊥ : Submodule k V)
      else F.spaces ⟨i.val - 1, by omega⟩ :=
    fun i v hv => by simp only [e₂, glvToLinearEquiv_toLinearMap]; exact hu₂.2 i v hv
  have hcomp_eq : d₁.toLinearMap.comp e₁.toLinearMap =
    d₂.toLinearMap.comp e₂.toLinearMap := by
    simp only [d₁, d₂, e₁, e₂, glvToLinearEquiv_toLinearMap]
    have : (↑(m₁ * u₁) : V →ₗ[k] V) = (↑(m₂ * u₂) : V →ₗ[k] V) := by rw [heq]
    simpa [Units.val_mul] using this
  have ⟨hd_eq, he_eq⟩ := SemidirectDecompositionProperty.unique_decomp_linear
    F F' hopp hlen hcov d₁ d₂ e₁ e₂ hd₁_F hd₁_F' hd₂_F hd₂_F' he₁_F he₁_unip he₂_F he₂_unip hcomp_eq
  constructor
  · have := congr_arg linearEquivToGLV hd_eq
    rwa [linearEquivToGLV_glvToLinearEquiv, linearEquivToGLV_glvToLinearEquiv] at this
  · have := congr_arg linearEquivToGLV he_eq
    rwa [linearEquivToGLV_glvToLinearEquiv, linearEquivToGLV_glvToLinearEquiv] at this



/--
[CompleteFlagPairsAreGLEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma CompleteFlagPairsAreGLEquivalent
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
  [CompleteFlagPairEquivalenceProperty k V] :
-- imply
  ∀ (F₁ F₂ : Flag k V) (F'₁ F'₂ : Flag k V) (_ : Flag.isOppositeFlag F₁ F'₁) (_ : Flag.isOppositeFlag F₂ F'₂), F₁.sameType F₂ → ∃ (g : GLV k V) (hlen : F₁.len = F₂.len) (hlen' : F'₁.len = F'₂.len), (∀ i : Fin F₁.len, (F₁.spaces i).map (↑g : V →ₗ[k] V) = F₂.spaces (i.cast hlen)) ∧ (∀ i : Fin F'₁.len, (F'₁.spaces i).map (↑g : V →ₗ[k] V) = F'₂.spaces (i.cast hlen')) := by
-- proof
  intro F₁ F₂ F'₁ F'₂ h₁ h₂ hst
  obtain ⟨e, hlen, hlen', he_F, he_F'⟩ :=
    CompleteFlagPairEquivalenceProperty.equiv_linear F₁ F₂ F'₁ F'₂ h₁ h₂ hst
  refine ⟨linearEquivToGLV e, hlen, hlen', fun i => ?_, fun i => ?_⟩
  · rw [linearEquivToGLV_val]; exact he_F i
  · rw [linearEquivToGLV_val]; exact he_F' i


/--
[linearEquivToGLV_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma linearEquivToGLV_val_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {e : V ≃ₗ[k] V} :
-- imply
  (↑(linearEquivToGLV e) : V →ₗ[k] V) = e.toLinearMap := by
-- proof
  apply GeometricAlgebra.linearEquivToGLV_val e

/--
[glvToLinearEquiv_toLinearMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma glvToLinearEquiv_toLinearMap_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {g : GLV k V} :
-- imply
  (glvToLinearEquiv g).toLinearMap = (↑g : V →ₗ[k] V) := by
-- proof
  apply GeometricAlgebra.glvToLinearEquiv_toLinearMap g

/--
[map_inv_of_map_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma map_inv_of_map_eq_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {e : V ≃ₗ[k] V}
  {W : Submodule k V}
-- given
  (h : W.map e.toLinearMap = W) :
-- imply
  W.map e.symm.toLinearMap = W := by
-- proof
  apply GeometricAlgebra.map_inv_of_map_eq e W h

/--
[map_inv_of_map_to](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma map_inv_of_map_to_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {g : GLV k V}
  {W₁ W₂ : Submodule k V}
-- given
  (h : W₁.map (↑g : V →ₗ[k] V) = W₂) :
-- imply
  W₂.map (↑(g⁻¹) : V →ₗ[k] V) = W₁ := by
-- proof
  apply GeometricAlgebra.map_inv_of_map_to g W₁ W₂ h

/--
[submodule_map_mul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma submodule_map_mul_eq_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {a b : GLV k V}
  {W : Submodule k V} :
-- imply
  W.map (↑(a * b) : V →ₗ[k] V) = (W.map (↑b : V →ₗ[k] V)).map (↑a : V →ₗ[k] V) := by
-- proof
  apply GeometricAlgebra.Flag.submodule_map_mul_eq a b W

/--
[truncate_len](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma truncate_len_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {F : Flag k V}
-- given
  (h : 1 ≤ F.len) :
-- imply
  (F.truncate h).len = F.len - 1 := by
-- proof
  apply GeometricAlgebra.Flag.truncate_len F h

/--
[truncateStart_len](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma truncateStart_len_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {F : Flag k V}
-- given
  (h : 1 ≤ F.len) :
-- imply
  (F.truncateStart h).len = F.len - 1 := by
-- proof
  apply GeometricAlgebra.Flag.truncateStart_len F h

/--
[truncate_spaces](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma truncate_spaces_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {F : Flag k V}
  {i : Fin (F.len - 1)}
-- given
  (h : 1 ≤ F.len) :
-- imply
  (F.truncate h).spaces i = F.spaces ⟨i.val, by omega⟩ := by
-- proof
  apply GeometricAlgebra.Flag.truncate_spaces F h i

/--
[truncateStart_spaces](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma truncateStart_spaces_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {F : Flag k V}
  {i : Fin (F.len - 1)}
-- given
  (h : 1 ≤ F.len) :
-- imply
  (F.truncateStart h).spaces i = F.spaces ⟨i.val + 1, by omega⟩ := by
-- proof
  apply GeometricAlgebra.Flag.truncateStart_spaces F h i

/--
[Flag.unipotent_levi_is_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma unipotent_levi_is_id_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {F F' : Flag k V}
  {e : V ≃ₗ[k] V}
-- given
  (hopp : Flag.isOppositeFlag F F')
  (hlen : 0 < F.len)
  (hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
  (he_F' : ∀ i : Fin F'.len, (F'.spaces i).map e.toLinearMap = F'.spaces i)
  (hunip : ∀ i : Fin F.len, ∀ v ∈ F.spaces i, e.toLinearMap v - v ∈ if _hh : (i : ℕ) = 0 then (⊥ : Submodule k V) else F.spaces ⟨i.val - 1, by omega⟩) :
-- imply
  e = LinearEquiv.refl k V := by
-- proof
  apply GeometricAlgebra.Flag.unipotent_levi_is_id F F' hopp hlen hcov e he_F' hunip

/--
[Flag.unique_decomp_linear_proof](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean)
-/
private lemma unique_decomp_linear_proof_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {F F' : Flag k V}
  {d₁ d₂ u₁ u₂ : V ≃ₗ[k] V}
-- given
  (hopp : Flag.isOppositeFlag F F')
  (hlen : 0 < F.len)
  (hcov : F.spaces ⟨F.len - 1, by omega⟩ = ⊤)
  (_hd₁_F : ∀ i : Fin F.len, (F.spaces i).map d₁.toLinearMap = F.spaces i)
  (hd₁_F' : ∀ i : Fin F'.len, (F'.spaces i).map d₁.toLinearMap = F'.spaces i)
  (_hd₂_F : ∀ i : Fin F.len, (F.spaces i).map d₂.toLinearMap = F.spaces i)
  (hd₂_F' : ∀ i : Fin F'.len, (F'.spaces i).map d₂.toLinearMap = F'.spaces i)
  (hu₁_F : ∀ i : Fin F.len, (F.spaces i).map u₁.toLinearMap = F.spaces i)
  (hu₁_unip : ∀ i : Fin F.len, ∀ v ∈ F.spaces i, u₁.toLinearMap v - v ∈ if _hh : (i : ℕ) = 0 then (⊥ : Submodule k V) else F.spaces ⟨i.val - 1, by omega⟩)
  (_hu₂_F : ∀ i : Fin F.len, (F.spaces i).map u₂.toLinearMap = F.spaces i)
  (hu₂_unip : ∀ i : Fin F.len, ∀ v ∈ F.spaces i, u₂.toLinearMap v - v ∈ if _hh : (i : ℕ) = 0 then (⊥ : Submodule k V) else F.spaces ⟨i.val - 1, by omega⟩)
  (hcomp : d₁.toLinearMap.comp u₁.toLinearMap = d₂.toLinearMap.comp u₂.toLinearMap) :
-- imply
  d₁ = d₂ ∧ u₁ = u₂ := by
-- proof
  apply GeometricAlgebra.Flag.unique_decomp_linear_proof F F' hopp hlen hcov d₁ d₂ u₁ u₂ _hd₁_F hd₁_F' _hd₂_F hd₂_F' hu₁_F hu₁_unip _hu₂_F hu₂_unip hcomp


-- created on 2026-10-23
-- updated on 2026-10-26
