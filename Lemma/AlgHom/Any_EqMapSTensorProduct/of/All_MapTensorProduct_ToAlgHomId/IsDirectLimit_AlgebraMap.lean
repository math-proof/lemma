import Mathlib
import sympy.Basic
import Instance.Algebra.DirectLimit
import Class.Mathlib_Algebra_IsDirectLimit
open scoped TensorProduct

private abbrev F
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  (i j : ι) (h : i ≤ j) : G i →ₗ[R₀] G j :=
  (f i j h).toLinearMap

private instance directedSystem_F
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  [DirectedSystem G fun i j h => ⇑(f i j h)] :
  DirectedSystem G fun i j h => ⇑(F f i j h) := by
  change DirectedSystem G fun i j h => ⇑(f i j h)
  infer_instance

private abbrev toR
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (i : ι) : G i →ₐ[R₀] R :=
  IsScalarTower.toAlgHom R₀ (G i) R

private lemma toR_apply
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (i : ι) (x : G i) :
  toR (R₀ := R₀) (R := R) i x = algebraMap (G i) R x := rfl

private lemma toR_f
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
  {i j : ι} (hij : i ≤ j) (x : G i) :
  toR (R₀ := R₀) (R := R) j (f i j hij x) = toR (R₀ := R₀) (R := R) i x :=
  hR.compatibility i j hij x

private noncomputable def limToR
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] [DecidableEq ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R)) :
  Module.DirectLimit G (F f) →ₗ[R₀] R :=
  Module.DirectLimit.lift R₀ ι G (F f) (fun i => (toR i).toLinearMap)
    (fun i j hij x => hR.compatibility i j hij x)

private lemma limToR_of
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] [DecidableEq ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
  (i : ι) (x : G i) :
  limToR f hR (Module.DirectLimit.of R₀ ι G (F f) i x) = algebraMap (G i) R x :=
  Module.DirectLimit.lift_of _ _ x

private lemma limToR_bijective
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] [DecidableEq ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R)) :
  Function.Bijective (limToR f hR) := by
  constructor
  ·
    rw [injective_iff_map_eq_zero]
    intro z hz
    induction z using Module.DirectLimit.induction_on with
    | ih i x =>
      rw [limToR_of] at hz
      have h0 : algebraMap (G i) R x = algebraMap (G i) R 0 := by rw [hz, map_zero]
      obtain ⟨k, hik, hik', hk⟩ := hR.inj i i x 0 h0
      have hk' : f i k hik x = 0 := by
        have : f i k hik' (0 : G i) = 0 := map_zero _
        rw [← this]
        apply hk
      rw [← Module.DirectLimit.of_f (f := F f) (hij := hik)]
      change Module.DirectLimit.of R₀ ι G (F f) k (f i k hik x) = 0
      rw [hk', map_zero]
  ·
    intro r
    obtain ⟨i, x, hx⟩ := hR.surj r
    exact ⟨Module.DirectLimit.of R₀ ι G (F f) i x, by rw [limToR_of]; apply hx⟩

private noncomputable def limEquiv
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] [DecidableEq ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R)) :
  Module.DirectLimit G (F f) ≃ₗ[R₀] R :=
  LinearEquiv.ofBijective (limToR f hR) (limToR_bijective f hR)

private lemma limEquiv_symm_algebraMap
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] [DecidableEq ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
  (i : ι) (x : G i) :
  (limEquiv f hR).symm (algebraMap (G i) R x) = Module.DirectLimit.of R₀ ι G (F f) i x := by
  rw [LinearEquiv.symm_apply_eq]
  apply (limToR_of f hR i x).symm

private abbrev mapT
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (B : Type w₂) [CommRing B] [Algebra R₀ B]
  (i : ι) : G i ⊗[R₀] B →ₐ[R₀] R ⊗[R₀] B :=
  Algebra.TensorProduct.map (toR i) (AlgHom.id R₀ B)

private abbrev stepT
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  (B : Type w₂) [CommRing B] [Algebra R₀ B]
  {i j : ι} (hij : i ≤ j) : G i ⊗[R₀] B →ₐ[R₀] G j ⊗[R₀] B :=
  Algebra.TensorProduct.map (f i j hij) (AlgHom.id R₀ B)

private lemma mapT_eq_rTensor
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (B : Type w₂) [CommRing B] [Algebra R₀ B]
  (i : ι) (x : G i ⊗[R₀] B) :
  mapT (R := R) B i x = (toR (R := R) i).toLinearMap.rTensor B x := by
  induction x using TensorProduct.inductionOn with
  | tmul g b =>
    rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul, AlgHom.id_apply]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]

private lemma stepT_eq_rTensor
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  (B : Type w₂) [CommRing B] [Algebra R₀ B]
  {i j : ι} (hij : i ≤ j) (x : G i ⊗[R₀] B) :
  stepT f B hij x = (F f i j hij).rTensor B x := by
  induction x using TensorProduct.inductionOn with
  | tmul g b =>
    rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul, AlgHom.id_apply]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]

private lemma mapT_stepT
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
  (B : Type w₂) [CommRing B] [Algebra R₀ B]
  {i j : ι} (hij : i ≤ j) (x : G i ⊗[R₀] B) :
  mapT (R := R) B j (stepT f B hij x) = mapT B i x := by
  induction x using TensorProduct.inductionOn with
  | tmul g b =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul, toR_f f hR, AlgHom.id_apply]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]

private lemma stepT_stepT
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  [DirectedSystem G fun i j h => ⇑(f i j h)]
  (B : Type w₂) [CommRing B] [Algebra R₀ B]
  {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (x : G i ⊗[R₀] B) :
  stepT f B hjk (stepT f B hij x) = stepT f B (hij.trans hjk) x := by
  induction x using TensorProduct.inductionOn with
  | tmul g b =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul]
    congr 1
    apply DirectedSystem.map_map (f := fun i j h => ⇑(f i j h)) hij hjk g
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]

private noncomputable def Φ
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] [DecidableEq ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
  (B : Type w₂) [CommRing B] [Algebra R₀ B] :
  R ⊗[R₀] B ≃ₗ[R₀] Module.DirectLimit (fun i => G i ⊗[R₀] B)
    (fun i j h => (F f i j h).rTensor B) :=
  LinearEquiv.trans ((limEquiv f hR).symm.rTensor B) (TensorProduct.directLimitLeft (F f) B)

private lemma Φ_mapT
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] [DecidableEq ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
  (B : Type w₂) [CommRing B] [Algebra R₀ B]
  (i : ι) (x : G i ⊗[R₀] B) :
  Φ f hR B (mapT B i x) =
    Module.DirectLimit.of R₀ ι (fun i => G i ⊗[R₀] B)
      (fun i j h => (F f i j h).rTensor B) i x := by
  induction x using TensorProduct.inductionOn with
  | tmul g b =>
    rw [Algebra.TensorProduct.map_tmul]
    change TensorProduct.directLimitLeft (F f) B
      (((limEquiv f hR).symm.rTensor B) (toR i g ⊗ₜ[R₀] b)) = _
    rw [LinearEquiv.rTensor_tmul, toR_apply, limEquiv_symm_algebraMap,
      TensorProduct.directLimitLeft_tmul_of]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

private lemma exists_mapT_eq
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] [DecidableEq ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
  (B : Type w₂) [CommRing B] [Algebra R₀ B]
  (z : R ⊗[R₀] B) :
  ∃ (i : ι) (x : G i ⊗[R₀] B), mapT B i x = z := by
  obtain ⟨i, y, hy⟩ := Module.DirectLimit.exists_of (Φ f hR B z)
  refine ⟨i, y, (Φ f hR B).injective ?_⟩
  rw [Φ_mapT, hy]

private lemma exists_stepT_eq_zero
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] [DecidableEq ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
  (B : Type w₂) [CommRing B] [Algebra R₀ B]
  {i : ι} (x : G i ⊗[R₀] B) (hx : mapT (R := R) B i x = 0) :
  ∃ (j : ι) (hij : i ≤ j), stepT f B hij x = 0 := by
  have h0 : Module.DirectLimit.of R₀ ι (fun i => G i ⊗[R₀] B)
      (fun i j h => (F f i j h).rTensor B) i x = 0 := by
    rw [← Φ_mapT f hR, hx, map_zero]
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact h0
  refine ⟨j, hij, ?_⟩
  rw [stepT_eq_rTensor]
  apply hj

private lemma exists_common_lift
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] [DecidableEq ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
  (B : Type w₂) [CommRing B] [Algebra R₀ B]
  {n : ℕ} (b : Fin n → R ⊗[R₀] B) :
  ∃ (i : ι) (y : Fin n → G i ⊗[R₀] B), ∀ k, mapT B i (y k) = b k := by
  choose idx x hx using fun k => exists_mapT_eq f hR B (b k)
  obtain ⟨M, hM⟩ := Finset.exists_le (Finset.univ.image idx)
  have hle : ∀ k, idx k ≤ M := fun k => hM _ (Finset.mem_image_of_mem idx (Finset.mem_univ k))
  refine ⟨M, fun k => stepT f B (hle k) (x k), fun k => ?_⟩
  rw [mapT_stepT f hR, hx]

private lemma exists_common_kill
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] [DecidableEq ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
  (B : Type w₂) [CommRing B] [Algebra R₀ B]
  {i : ι} {m : ℕ} (x : Fin m → G i ⊗[R₀] B) (hx : ∀ l, mapT (R := R) B i (x l) = 0) :
  ∃ (j : ι) (hij : i ≤ j), ∀ l, stepT f B hij (x l) = 0 := by
  choose idx hidx hzero using fun l => exists_stepT_eq_zero f hR B (x l) (hx l)
  obtain ⟨M, hM⟩ := Finset.exists_le (insert i (Finset.univ.image idx))
  have hiM : i ≤ M := hM _ (Finset.mem_insert_self _ _)
  have hle : ∀ l, idx l ≤ M := fun l =>
    hM _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem idx (Finset.mem_univ l)))
  refine ⟨M, hiM, fun l => ?_⟩
  have : stepT f B hiM (x l) = stepT f B (hle l) (stepT f B (hidx l) (x l)) := by
    rw [stepT_stepT]
  rw [this, hzero, map_zero]

private lemma step_apply_eq
  {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j)
  [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R]
  [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
  (A : Type w₁) [CommRing A] [Algebra R₀ A] [Algebra.FiniteType R₀ A]
  (B : Type w₂) [CommRing B] [Algebra R₀ B]
  {i : ι} (φ₁ φ₂ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B)
  (h : ∀ x : G i ⊗[R₀] A, mapT (R := R) B i (φ₁ x) = mapT B i (φ₂ x)) :
  ∃ (j : ι) (hij : i ≤ j), ∀ x : G i ⊗[R₀] A, stepT f B hij (φ₁ x) = stepT f B hij (φ₂ x) := by
  classical
  obtain ⟨n, g, hg⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R₀) (S := A)).mp ‹_›
  obtain ⟨j, hij, hkill⟩ := exists_common_kill f hR B
    (fun k : Fin n => φ₁ ((1 : G i) ⊗ₜ[R₀] g (MvPolynomial.X k)) -
      φ₂ ((1 : G i) ⊗ₜ[R₀] g (MvPolynomial.X k)))
    (fun k => by rw [map_sub, h, sub_self])
  refine ⟨j, hij, ?_⟩
  let H : (G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B) → (G i ⊗[R₀] A →ₐ[R₀] G j ⊗[R₀] B) :=
    fun ψ => (stepT f B hij).comp (ψ.restrictScalars R₀)
  suffices hH : H φ₁ = H φ₂ by
    intro x
    apply AlgHom.congr_fun hH
  have hleft : ∀ (ψ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B) (a : G i),
      ψ (a ⊗ₜ[R₀] (1 : A)) = a ⊗ₜ[R₀] (1 : B) := by
    intro ψ a
    have h1 : a ⊗ₜ[R₀] (1 : A) = algebraMap (G i) (G i ⊗[R₀] A) a := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have h2 : a ⊗ₜ[R₀] (1 : B) = algebraMap (G i) (G i ⊗[R₀] B) a := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [h1, AlgHom.commutes, ← h2]
  apply Algebra.TensorProduct.ext
  ·
    ext a
    change stepT f B hij (φ₁ (a ⊗ₜ[R₀] (1 : A))) = stepT f B hij (φ₂ (a ⊗ₜ[R₀] (1 : A)))
    rw [hleft, hleft]
  ·
    have key : (((H φ₁).restrictScalars R₀).comp Algebra.TensorProduct.includeRight).comp g =
        (((H φ₂).restrictScalars R₀).comp Algebra.TensorProduct.includeRight).comp g := by
      refine MvPolynomial.algHom_ext fun k => ?_
      change stepT f B hij (φ₁ ((1 : G i) ⊗ₜ[R₀] g (MvPolynomial.X k))) =
        stepT f B hij (φ₂ ((1 : G i) ⊗ₜ[R₀] g (MvPolynomial.X k)))
      rw [← sub_eq_zero, ← map_sub]
      apply hkill
    apply AlgHom.ext
    intro a
    obtain ⟨p, rfl⟩ := hg a
    apply AlgHom.congr_fun key

/--
[Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.lean)
-/
@[path]
private lemma main
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R₀ : Type u₀} [CommRing R₀]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  {f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j} [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R] [∀ i, IsScalarTower R₀ (G i) R]
  {A : Type w₁} [CommRing A] [Algebra R₀ A] [Algebra.FiniteType R₀ A]
  {B : Type w₂} [CommRing B] [Algebra R₀ B]
  {i : ι} {φ₁ φ₂ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B}
-- given
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
  (h : ∀ x : G i ⊗[R₀] A,
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B) (φ₁ x) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B) (φ₂ x)) :
-- imply
  ∃ (j : ι) (hij : i ≤ j), ∀ x : G i ⊗[R₀] A,
    Algebra.TensorProduct.map (f i j hij) (AlgHom.id R₀ B) (φ₁ x) =
      Algebra.TensorProduct.map (f i j hij) (AlgHom.id R₀ B) (φ₂ x) := by
-- proof
  classical
  apply step_apply_eq f hR A B φ₁ φ₂ h

-- created on 2026-10-20
