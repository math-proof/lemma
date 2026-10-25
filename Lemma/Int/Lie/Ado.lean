import Mathlib
import sympy.Basic
import Theorem.Algebra.Lie.Ado.Part5
open LieAlgebra
open scoped TensorProduct
open MathlibExt.Algebra.Lie.LandmarkWanted


namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[ado_transport_fin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma ado_transport_fin
  {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [Module.Finite K V]
  (ρ : L →ₗ⁅K⁆ Module.End K V) (hρ : Function.Injective ρ) :
  ∃ (n : ℕ) (ρ' : L →ₗ⁅K⁆ Module.End K (Fin n → K)),
    Function.Injective ρ' := by
  let _ : Module.Free K V := Module.Free.of_divisionRing K V
  let e := (Module.finBasis K V).equivFun
  refine ⟨Module.finrank K V, e.lieConj.comp ρ, ?_⟩
  exact e.lieConj.injective.comp hρ

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoDirectSum_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoDirectSum_eq_zero_iff
  {K L V W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (ρ : L →ₗ⁅K⁆ Module.End K V) (σ : L →ₗ⁅K⁆ Module.End K W) (x : L) :
  adoDirectSum ρ σ x = 0 ↔ ρ x = 0 ∧ σ x = 0 := by
  constructor
  · intro h
    constructor
    · ext v
      exact congrArg Prod.fst (LinearMap.congr_fun h (v, 0))
    · ext w
      exact congrArg Prod.snd (LinearMap.congr_fun h (0, w))
  · rintro ⟨hρ, hσ⟩
    change (ρ x).prodMap (σ x) = 0
    rwa [hρ, hσ]

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoAbelianShear_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoAbelianShear_injective
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [IsLieAbelian L] :
  Function.Injective (adoAbelianShear (K := K) (L := L)) := by
  intro x y h
  have hxy := LinearMap.congr_fun h (0, 1)
  simpa [adoAbelianShear, adoAbelianShearLinear] using congrArg Prod.fst hxy

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoAbelianShear_mul_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoAbelianShear_mul_eq_zero
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [IsLieAbelian L]
  (x y : L) :
  adoAbelianShear (K := K) x * adoAbelianShear (K := K) y = 0 := by
  ext p <;> simp [adoAbelianShear, adoAbelianShearLinear, Module.End.mul_apply]

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[ado_faithful_of_faithful_on_center](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma ado_faithful_of_faithful_on_center
  {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V]
  (ρ : L →ₗ⁅K⁆ Module.End K V)
  (hρ : ∀ x : L, x ∈ LieAlgebra.center K L → ρ x = 0 → x = 0) :
  Function.Injective (adoDirectSum ρ (LieModule.toEnd K L L)) := by
  intro x y hxy
  have hzero : adoDirectSum ρ (LieModule.toEnd K L L) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨hρzero, hadzero⟩ :=
    (adoDirectSum_eq_zero_iff ρ (LieModule.toEnd K L L) (x - y)).mp hzero
  have hcenter : x - y ∈ LieAlgebra.center K L := by
    rw [← LieAlgebra.self_module_ker_eq_center K L]
    rw [LieModule.mem_ker]
    intro z
    have hz := LinearMap.congr_fun hadzero z
    simpa only [LieModule.toEnd_apply_apply, LinearMap.zero_apply] using hz
  exact sub_eq_zero.mp (hρ (x - y) hcenter hρzero)

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoWord_append](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoWord_append
  {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
  {d : ℕ} (b : Module.Basis (Fin d) K L) (u v : List (Fin d)) :
  adoWord b (u ++ v) = adoWord b u * adoWord b v := by
  simp [adoWord, List.map_append]

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoWord_mem_wordsLt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoWord_mem_wordsLt
  {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
  {d : ℕ} (b : Module.Basis (Fin d) K L) {w : List (Fin d)} {n : ℕ}
  (hw : w.length < n) : adoWord b w ∈ adoWordsLt b n :=
  ⟨w, hw, rfl⟩

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoMul_word_mem_span_wordsLt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoMul_word_mem_span_wordsLt
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {d : ℕ} (b : Module.Basis (Fin d) K L) {u : adoUEA K L} {n : ℕ}
  (hu : u ∈ Submodule.span K (adoWordsLt b n)) (v : List (Fin d)) :
  u * adoWord b v ∈ Submodule.span K (adoWordsLt b (n + v.length)) := by
  refine Submodule.span_induction (p := fun u _ =>
    u * adoWord b v ∈ Submodule.span K (adoWordsLt b (n + v.length))) ?_ ?_ ?_ ?_ hu
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := hu
    rw [← adoWord_append]
    apply Submodule.subset_span
    exact adoWord_mem_wordsLt b (by simp; omega)
  · simp
  · intro x y _ _ hx hy
    simpa [add_mul] using Submodule.add_mem _ hx hy
  · intro c x _ hx
    simpa [Algebra.smul_mul_assoc] using Submodule.smul_mem
      (Submodule.span K (adoWordsLt b (n + v.length))) c hx

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoWord_mul_mem_span_wordsLt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoWord_mul_mem_span_wordsLt
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {d : ℕ} (b : Module.Basis (Fin d) K L) (v : List (Fin d))
  {u : adoUEA K L} {n : ℕ} (hu : u ∈ Submodule.span K (adoWordsLt b n)) :
  adoWord b v * u ∈ Submodule.span K (adoWordsLt b (v.length + n)) := by
  refine Submodule.span_induction (p := fun u _ =>
    adoWord b v * u ∈ Submodule.span K (adoWordsLt b (v.length + n))) ?_ ?_ ?_ ?_ hu
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := hu
    rw [← adoWord_append]
    apply Submodule.subset_span
    exact adoWord_mem_wordsLt b (by simp; omega)
  · simp
  · intro x y _ _ hx hy
    simpa [mul_add] using Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [Algebra.mul_smul_comm]
    exact Submodule.smul_mem _ c hx

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoIota_mem_span_wordsLt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoIota_mem_span_wordsLt
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {d : ℕ} (b : Module.Basis (Fin d) K L) (x : L) :
  UniversalEnvelopingAlgebra.ι K x ∈ Submodule.span K (adoWordsLt b 2) := by
  rw [← b.sum_repr x]
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.subset_span
  simpa [adoWord] using adoWord_mem_wordsLt b (w := [i]) (n := 2) (by simp)

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoWord_sub_word_mem_span_wordsLt_of_perm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoWord_sub_word_mem_span_wordsLt_of_perm
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {d : ℕ} (b : Module.Basis (Fin d) K L) {u v : List (Fin d)} (h : u.Perm v) :
  adoWord b u - adoWord b v ∈ Submodule.span K (adoWordsLt b u.length) := by
  induction h with
  | nil => simp
  | cons i h ih =>
    rw [adoWord_cons, adoWord_cons, ← mul_sub]
    have hm := adoWord_mul_mem_span_wordsLt b [i] ih
    simpa [Nat.add_comm] using hm
  | swap i j w =>
    simp only [adoWord_cons]
    rw [← mul_assoc, ← mul_assoc, ← sub_mul]
    have hrel :
      UniversalEnvelopingAlgebra.ι K (b j) * UniversalEnvelopingAlgebra.ι K (b i) -
        UniversalEnvelopingAlgebra.ι K (b i) * UniversalEnvelopingAlgebra.ι K (b j) =
        UniversalEnvelopingAlgebra.ι K ⁅b j, b i⁆ := by
      simpa only [Ring.lie_def] using
        (LieHom.map_lie (UniversalEnvelopingAlgebra.ι K) (b j) (b i)).symm
    rw [hrel]
    have hi := adoIota_mem_span_wordsLt b ⁅b j, b i⁆
    have hm := adoMul_word_mem_span_wordsLt b hi w
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm
  | trans h₁ h₂ ih₁ ih₂ =>
    have hsum := Submodule.add_mem _ ih₁ (by simpa [h₁.length_eq] using ih₂)
    rwa [sub_add_sub_cancel] at hsum

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoExists_replicate_perm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoExists_replicate_perm {d B : ℕ} [NeZero d] (w : List (Fin d))
  (h : d * B ≤ w.length) :
  ∃ i : Fin d, ∃ rest, w.Perm (List.replicate B i ++ rest) := by
  let v : List.Vector (Fin d) w.length := ⟨w, rfl⟩
  obtain ⟨i, hi⟩ := Fintype.exists_le_card_fiber_of_mul_le_card
    (fun j : Fin w.length => v.get j) (by simpa using h)
  have hicount : B ≤ w.count i := by
    rw [Fin.card_filter_univ_eq_vector_get_eq_count i v] at hi
    simpa [v] using hi
  have hsub : (List.replicate B i).Sublist w :=
    List.replicate_sublist_iff.mpr hicount
  obtain ⟨rest, hperm⟩ := hsub.exists_perm_append
  exact ⟨i, rest, hperm⟩

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoModWords_mul_word](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoModWords_mul_word
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {d : ℕ} (Q : Ideal (adoUEA K L)) [Q.IsTwoSided]
  (b : Module.Basis (Fin d) K L) {u : adoUEA K L} {n : ℕ}
  (hu : u ∈ adoModWords Q b n) (v : List (Fin d)) :
  u * adoWord b v ∈ adoModWords Q b (n + v.length) := by
  obtain ⟨q, hq, s, hs, rfl⟩ := Submodule.mem_sup.mp hu
  rw [add_mul]
  apply Submodule.add_mem
  · apply Submodule.mem_sup_left
    exact Q.mul_mem_right _ hq
  · apply Submodule.mem_sup_right
    exact adoMul_word_mem_span_wordsLt b hs v

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoLong_word_mem_modWords](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoLong_word_mem_modWords
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {d B : ℕ} [NeZero d] (Q : Ideal (adoUEA K L)) [Q.IsTwoSided]
  (b : Module.Basis (Fin d) K L)
  (hpow : ∀ i : Fin d,
    (UniversalEnvelopingAlgebra.ι K (b i)) ^ B ∈ adoModWords Q b B)
  (w : List (Fin d)) (hw : d * B ≤ w.length) :
  adoWord b w ∈ adoModWords Q b w.length := by
  obtain ⟨i, rest, hperm⟩ := adoExists_replicate_perm w hw
  let block := List.replicate B i ++ rest
  have hlen : block.length = w.length := hperm.length_eq.symm
  have hdiff : adoWord b w - adoWord b block ∈ adoModWords Q b w.length := by
    apply Submodule.mem_sup_right
    exact adoWord_sub_word_mem_span_wordsLt_of_perm b hperm
  have hblock : adoWord b block ∈ adoModWords Q b w.length := by
    have hm := adoModWords_mul_word Q b (hpow i) rest
    have hword : adoWord b block =
      (UniversalEnvelopingAlgebra.ι K (b i)) ^ B * adoWord b rest := by
      simp [block, adoWord]
    rw [hword]
    have hsum : B + rest.length = w.length := by simpa [block] using hlen
    rwa [hsum] at hm
  have heq : adoWord b w = (adoWord b w - adoWord b block) + adoWord b block := by abel
  rw [heq]
  exact Submodule.add_mem _ hdiff hblock

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoWord_mem_bounded_modWords](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoWord_mem_bounded_modWords
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {d B : ℕ} [NeZero d] (Q : Ideal (adoUEA K L)) [Q.IsTwoSided]
  (b : Module.Basis (Fin d) K L)
  (hpow : ∀ i : Fin d,
    (UniversalEnvelopingAlgebra.ι K (b i)) ^ B ∈ adoModWords Q b B)
  (w : List (Fin d)) : adoWord b w ∈ adoModWords Q b (d * B) := by
  induction hlen : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hw : w.length < d * B
    · apply Submodule.mem_sup_right
      exact Submodule.subset_span (adoWord_mem_wordsLt b hw)
    · have hlong := adoLong_word_mem_modWords Q b hpow w (Nat.le_of_not_gt hw)
      obtain ⟨q, hq, s, hs, hqs⟩ := Submodule.mem_sup.mp hlong
      rw [← hqs]
      apply Submodule.add_mem
      · exact Submodule.mem_sup_left hq
      · refine Submodule.span_induction (p := fun s _ => s ∈ adoModWords Q b (d * B))
        ?_ (Submodule.zero_mem _) (fun _ _ _ _ => Submodule.add_mem _)
        (fun c _ _ h => Submodule.smul_mem _ c h) hs
        rintro u ⟨v, hv, rfl⟩
        exact ih v.length (by simpa [hlen] using hv) v rfl

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoWord_mem_span_allWords](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoWord_mem_span_allWords
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {d : ℕ} (b : Module.Basis (Fin d) K L) (w : List (Fin d)) :
  adoWord b w ∈ Submodule.span K (adoAllWords b) :=
  Submodule.subset_span ⟨w, rfl⟩

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoSpan_allWords_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoSpan_allWords_mul
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {d : ℕ} (b : Module.Basis (Fin d) K L) {u v : adoUEA K L}
  (hu : u ∈ Submodule.span K (adoAllWords b))
  (hv : v ∈ Submodule.span K (adoAllWords b)) :
  u * v ∈ Submodule.span K (adoAllWords b) := by
  refine Submodule.span_induction (p := fun u _ =>
    u * v ∈ Submodule.span K (adoAllWords b)) ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨w, rfl⟩
    refine Submodule.span_induction (p := fun v _ =>
      adoWord b w * v ∈ Submodule.span K (adoAllWords b)) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨z, rfl⟩
      rw [← adoWord_append]
      exact adoWord_mem_span_allWords b (w ++ z)
    · simp
    · intro x y _ _ hx hy
      simpa [mul_add] using Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [Algebra.mul_smul_comm]
      exact Submodule.smul_mem _ c hx
  · simp
  · intro x y _ _ hx hy
    simpa [add_mul] using Submodule.add_mem _ hx hy
  · intro c x _ hx
    simpa [Algebra.smul_mul_assoc] using Submodule.smul_mem
      (Submodule.span K (adoAllWords b)) c hx

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoIota_mem_span_allWords](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoIota_mem_span_allWords
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {d : ℕ} (b : Module.Basis (Fin d) K L) (x : L) :
  UniversalEnvelopingAlgebra.ι K x ∈ Submodule.span K (adoAllWords b) := by
  rw [← b.sum_repr x]
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  simpa [adoWord] using adoWord_mem_span_allWords b [i]

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoUEA_mem_span_allWords](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoUEA_mem_span_allWords
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {d : ℕ} (b : Module.Basis (Fin d) K L) (u : adoUEA K L) :
  u ∈ Submodule.span K (adoAllWords b) := by
  obtain ⟨t, ht⟩ := RingCon.mkₐ_surjective (α := K)
    (UniversalEnvelopingAlgebra.ringCon K L) u
  subst u
  change UniversalEnvelopingAlgebra.mkAlgHom K L t ∈ Submodule.span K (adoAllWords b)
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    change algebraMap K (adoUEA K L) r ∈ Submodule.span K (adoAllWords b)
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (by simpa using adoWord_mem_span_allWords b [])
  | ι x => exact adoIota_mem_span_allWords b x
  | mul x y hx hy => exact adoSpan_allWords_mul b hx hy
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoUEA_mem_bounded_modWords](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoUEA_mem_bounded_modWords
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {d B : ℕ} [NeZero d] (Q : Ideal (adoUEA K L)) [Q.IsTwoSided]
  (b : Module.Basis (Fin d) K L)
  (hpow : ∀ i : Fin d,
    (UniversalEnvelopingAlgebra.ι K (b i)) ^ B ∈ adoModWords Q b B)
  (u : adoUEA K L) : u ∈ adoModWords Q b (d * B) := by
  refine Submodule.span_induction (p := fun u _ => u ∈ adoModWords Q b (d * B))
    ?_ (Submodule.zero_mem _) (fun _ _ _ _ => Submodule.add_mem _)
    (fun c _ _ h => Submodule.smul_mem _ c h) (adoUEA_mem_span_allWords b u)
  rintro _ ⟨w, rfl⟩
  exact adoWord_mem_bounded_modWords Q b hpow w

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoWordsLt_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoWordsLt_finite
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {d : ℕ} (b : Module.Basis (Fin d) K L) (n : ℕ) :
  (adoWordsLt b n).Finite := by
  have h := (List.finite_length_lt (Fin d) n).image (adoWord b)
  apply h.subset
  rintro u ⟨w, hw, rfl⟩
  exact ⟨w, hw, rfl⟩

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoQuotient_finite_of_power_relations](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoQuotient_finite_of_power_relations
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {d B : ℕ} (Q : Ideal (adoUEA K L)) [Q.IsTwoSided]
  (b : Module.Basis (Fin d) K L)
  (hpow : ∀ i : Fin d,
    (UniversalEnvelopingAlgebra.ι K (b i)) ^ B ∈ adoModWords Q b B) :
  Module.Finite K (adoUEA K L ⧸
    (Q : Submodule (adoUEA K L) (adoUEA K L)).restrictScalars K) := by
  let qK := (Q : Submodule (adoUEA K L) (adoUEA K L)).restrictScalars K
  by_cases hd : d = 0
  · subst d
    have hall : adoAllWords b = {1} := by
      ext u
      constructor
      · rintro ⟨w, rfl⟩
        have hw : w = [] := Subsingleton.elim w []
        subst w
        simp
      · rintro (rfl)
        exact ⟨[], by simp⟩
    let S := Submodule.span K (adoAllWords b)
    have hS : S = ⊤ := by
      apply top_unique
      intro u _
      exact adoUEA_mem_span_allWords b u
    let _ : Module.Finite K S := Module.Finite.span_of_finite K (by
      rw [hall]
      exact Set.finite_singleton 1)
    have hsurj : Function.Surjective S.subtype := by
      intro u
      refine ⟨⟨u, ?_⟩, rfl⟩
      rwa [hS]
    let _ : Module.Finite K (adoUEA K L) :=
      Module.Finite.of_surjective S.subtype hsurj
    exact Module.Finite.of_surjective qK.mkQ
      (Submodule.Quotient.mk_surjective qK)
  · let _ : NeZero d := ⟨hd⟩
    let S := Submodule.span K (adoWordsLt b (d * B))
    let f : S →ₗ[K] adoUEA K L ⧸ qK := qK.mkQ.comp S.subtype
    let _ : Module.Finite K S :=
      Module.Finite.span_of_finite K (adoWordsLt_finite b (d * B))
    apply Module.Finite.of_surjective f
    intro z
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective qK z
    have hu := adoUEA_mem_bounded_modWords Q b hpow u
    obtain ⟨q, hq, s, hs, hqs⟩ := Submodule.mem_sup.mp hu
    refine ⟨⟨s, hs⟩, ?_⟩
    apply (Submodule.Quotient.eq qK).mpr
    change s - u ∈ qK
    rw [← hqs]
    simpa using qK.neg_mem hq

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoUEA_lift_preserves](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoUEA_lift_preserves
  {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  (W : LieSubmodule K L V) (u : adoUEA K L) {v : V} (hv : v ∈ W) :
  UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V) u v ∈ W := by
  let φ := UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V)
  obtain ⟨t, ht⟩ := RingCon.mkₐ_surjective (α := K)
    (UniversalEnvelopingAlgebra.ringCon K L) u
  subst u
  change φ (UniversalEnvelopingAlgebra.mkAlgHom K L t) v ∈ W
  revert v
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    intro v hv
    simpa using W.smul_mem r hv
  | ι x =>
    intro v hv
    simpa [φ] using W.lie_mem hv
  | mul x y hx hy =>
    intro v hv
    rw [map_mul, map_mul, Module.End.mul_apply]
    change φ (UniversalEnvelopingAlgebra.mkAlgHom K L x)
      (φ (UniversalEnvelopingAlgebra.mkAlgHom K L y) v) ∈ W
    exact hx (hy hv)
  | add x y hx hy =>
    intro v hv
    rw [map_add, map_add]
    simpa using W.add_mem (hx hv) (hy hv)

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoTwoSidedSpan_lowers_lcs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoTwoSidedSpan_lowers_lcs
  {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  (I : LieIdeal K L) (S : Set (adoUEA K L))
  (hS : ∀ s ∈ S, ∀ j v, v ∈ I.lcs V j →
    UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V) s v ∈
      I.lcs V (j + 1))
  {t : adoUEA K L} (ht : t ∈ TwoSidedIdeal.span S) (j : ℕ) {v : V}
  (hv : v ∈ I.lcs V j) :
  UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V) t v ∈
    I.lcs V (j + 1) := by
  let φ := UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V)
  refine TwoSidedIdeal.span_induction (p := fun t _ =>
    ∀ j v, v ∈ I.lcs V j → φ t v ∈ I.lcs V (j + 1))
    ?_ ?_ ?_ ?_ ?_ ?_ ht j v hv
  · intro s hs
    exact hS s hs
  · simp
  · intro x y _ _ hx hy j v hv
    simpa using (I.lcs V (j + 1)).add_mem (hx j v hv) (hy j v hv)
  · intro x _ hx j v hv
    simpa using (I.lcs V (j + 1)).neg_mem (hx j v hv)
  · intro a x _ hx j v hv
    rw [map_mul, Module.End.mul_apply]
    change φ a (φ x v) ∈ I.lcs V (j + 1)
    exact adoUEA_lift_preserves (I.lcs V (j + 1)) a (hx j v hv)
  · intro b x _ hx j v hv
    rw [map_mul, Module.End.mul_apply]
    change φ x (φ b v) ∈ I.lcs V (j + 1)
    exact hx j (φ b v) (adoUEA_lift_preserves (I.lcs V j) b hv)

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoIdealPower_lowers_lcs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoIdealPower_lowers_lcs
  {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  (I : LieIdeal K L) (S : Set (adoUEA K L))
  (hS : ∀ s ∈ S, ∀ j v, v ∈ I.lcs V j →
    UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V) s v ∈
      I.lcs V (j + 1))
  (k j : ℕ) {t : adoUEA K L}
  (ht : t ∈ (TwoSidedIdeal.span S).asIdeal ^ k) {v : V}
  (hv : v ∈ I.lcs V j) :
  UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V) t v ∈
    I.lcs V (j + k) := by
  let φ := UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V)
  induction k generalizing t j v with
  | zero =>
    simpa using adoUEA_lift_preserves (I.lcs V j) t hv
  | succ k ih =>
    rw [Ideal.IsTwoSided.pow_succ] at ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro x hx y hy
      rw [map_mul, Module.End.mul_apply]
      change φ x (φ y v) ∈ I.lcs V (j + (k + 1))
      have hyv := ih j hy hv
      have hxv := adoTwoSidedSpan_lowers_lcs I S hS
        (TwoSidedIdeal.mem_asIdeal.mp hx) (j + k) hyv
      simpa [Nat.add_assoc] using hxv
    · intro x y hx hy
      simpa using (I.lcs V (j + (k + 1))).add_mem hx hy

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoIdealPower_le_ker_lift](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoIdealPower_le_ker_lift
  {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  (I : LieIdeal K L) (S : Set (adoUEA K L))
  (hS : ∀ s ∈ S, ∀ j v, v ∈ I.lcs V j →
    UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V) s v ∈
      I.lcs V (j + 1))
  (k : ℕ) (hk : I.lcs V k = ⊥) :
  (((TwoSidedIdeal.span S).asIdeal ^ k : Ideal (adoUEA K L)) :
    Submodule (adoUEA K L) (adoUEA K L)).restrictScalars K ≤
      LinearMap.ker (UniversalEnvelopingAlgebra.lift K
        (LieModule.toEnd K L V)).toLinearMap := by
  intro t ht
  rw [LinearMap.mem_ker]
  ext v
  rw [LinearMap.zero_apply]
  have h := adoIdealPower_lowers_lcs I S hS k 0 ht (v := v)
    (by simp [LieIdeal.lcs_zero])
  simpa [hk] using h

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoDerivation_pow_mul_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoDerivation_pow_mul_eq_zero
  {K A : Type*} [Field K] [Ring A] [Algebra K A]
  (d : Module.End K A) (hd : ∀ x y, d (x * y) = x * d y + d x * y)
  {x y : A} {a b : ℕ} (hx : (d ^ a) x = 0) (hy : (d ^ b) y = 0) :
  (d ^ (a + b)) (x * y) = 0 := by
  induction h : a + b using Nat.strong_induction_on generalizing a b x y with
  | h n ih =>
    subst n
    obtain rfl | a := a
    · have hx0 : x = 0 := by simpa using hx
      subst x
      simp
    obtain rfl | b := b
    · have hy0 : y = 0 := by simpa using hy
      subst y
      simp
    have hdx : (d ^ a) (d x) = 0 := by
      simpa [pow_succ, Module.End.mul_apply] using hx
    have hdy : (d ^ b) (d y) = 0 := by
      simpa [pow_succ, Module.End.mul_apply] using hy
    have h₁ : (d ^ (a.succ + b)) (x * d y) = 0 :=
      ih (a.succ + b) (by omega) (a := a.succ) (b := b) hx hdy rfl
    have h₂ : (d ^ (a + b.succ)) (d x * y) = 0 :=
      ih (a + b.succ) (by omega) (a := a) (b := b.succ) hdx hy rfl
    have h₁' : (d ^ (a + b + 1)) (x * d y) = 0 := by
      rwa [show a + b + 1 = a.succ + b by omega]
    have h₂' : (d ^ (a + b + 1)) (d x * y) = 0 := by
      rwa [show a + b + 1 = a + b.succ by omega]
    rw [show a.succ + b.succ = (a + b + 1) + 1 by omega,
      pow_succ, Module.End.mul_apply, hd, map_add]
    rw [h₁', h₂', add_zero]

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoDerivation_locallyNilpotent_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoDerivation_locallyNilpotent_add
  {K A : Type*} [Field K] [AddCommGroup A] [Module K A]
  (d : Module.End K A) {x y : A}
  (hx : ∃ n, (d ^ n) x = 0) (hy : ∃ n, (d ^ n) y = 0) :
  ∃ n, (d ^ n) (x + y) = 0 := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  rw [map_add]
  have hax : (d ^ (a + b)) x = 0 := by
    rw [show a + b = b + a by omega, pow_add, Module.End.mul_apply, ha, map_zero]
  have hby : (d ^ (a + b)) y = 0 := by
    rw [pow_add, Module.End.mul_apply, hb, map_zero]
  rw [hax, hby, add_zero]

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoDerivation_locallyNilpotent_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoDerivation_locallyNilpotent_mul
  {K A : Type*} [Field K] [Ring A] [Algebra K A]
  (d : Module.End K A) (hd : ∀ x y, d (x * y) = x * d y + d x * y)
  {x y : A} (hx : ∃ n, (d ^ n) x = 0) (hy : ∃ n, (d ^ n) y = 0) :
  ∃ n, (d ^ n) (x * y) = 0 := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, adoDerivation_pow_mul_eq_zero d hd ha hb⟩

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoUEA_derivation_locallyNilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoUEA_derivation_locallyNilpotent
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  (D : Module.End K L) (d : Module.End K (adoUEA K L))
  (hd : ∀ u v, d (u * v) = u * d v + d u * v)
  (hι : ∀ x, d (UniversalEnvelopingAlgebra.ι K x) =
    UniversalEnvelopingAlgebra.ι K (D x))
  (hD : IsNilpotent D) (u : adoUEA K L) :
  ∃ n, (d ^ n) u = 0 := by
  have hd1 : d 1 = 0 := by
    have h := hd 1 1
    simp only [one_mul, mul_one] at h
    have h' := congrArg (fun z => z - d 1) h
    simpa using h'.symm
  have hscalar (c : K) : d (algebraMap K (adoUEA K L) c) = 0 := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hd1, smul_zero]
  have hιpow (n : ℕ) (x : L) :
    (d ^ n) (UniversalEnvelopingAlgebra.ι K x) =
      UniversalEnvelopingAlgebra.ι K ((D ^ n) x) := by
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, hι, pow_succ,
        Module.End.mul_apply]
      exact ih (D x)
  obtain ⟨r, hr⟩ := hD
  obtain ⟨t, ht⟩ := RingCon.mkₐ_surjective (α := K)
    (UniversalEnvelopingAlgebra.ringCon K L) u
  subst u
  change ∃ n, (d ^ n) (UniversalEnvelopingAlgebra.mkAlgHom K L t) = 0
  induction t using TensorAlgebra.induction with
  | algebraMap c =>
    refine ⟨1, ?_⟩
    change d (algebraMap K (adoUEA K L) c) = 0
    exact hscalar c
  | ι x =>
    refine ⟨r, ?_⟩
    change (d ^ r) (UniversalEnvelopingAlgebra.ι K x) = 0
    rw [hιpow, LinearMap.congr_fun hr x, LinearMap.zero_apply, map_zero]
  | mul x y hx hy =>
    rw [map_mul]
    exact adoDerivation_locallyNilpotent_mul d hd hx hy
  | add x y hx hy =>
    rw [map_add]
    exact adoDerivation_locallyNilpotent_add d hx hy

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoEnd_isNilpotent_of_locallyNilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoEnd_isNilpotent_of_locallyNilpotent
  {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [Module.Finite K M]
  (f : Module.End K M) (hlocal : ∀ x, ∃ n, (f ^ n) x = 0) :
  IsNilpotent f := by
  classical
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := K) (M := M)
  choose e he using fun i : Fin m => hlocal (s i)
  let N := ∑ i : Fin m, e i
  have hei (i : Fin m) : e i ≤ N := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hkill (i : Fin m) : (f ^ N) (s i) = 0 := by
    have hi := hei i
    rw [show N = (N - e i) + e i by omega, pow_add, Module.End.mul_apply,
      he i, map_zero]
  refine ⟨N, LinearMap.ker_eq_top.mp ?_⟩
  apply top_unique
  rw [← hs]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change (f ^ N) (s i) = 0
  exact hkill i

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoUEA_derivation_mem_ideal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoUEA_derivation_mem_ideal
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  (d : Module.End K (adoUEA K L))
  (hd : ∀ u v, d (u * v) = u * d v + d u * v)
  (T : Ideal (adoUEA K L)) [T.IsTwoSided]
  (hι : ∀ x, d (UniversalEnvelopingAlgebra.ι K x) ∈ T)
  (u : adoUEA K L) : d u ∈ T := by
  have hd1 : d 1 = 0 := by
    have h := hd 1 1
    simp only [one_mul, mul_one] at h
    have h' := congrArg (fun z => z - d 1) h
    simpa using h'.symm
  obtain ⟨t, ht⟩ := RingCon.mkₐ_surjective (α := K)
    (UniversalEnvelopingAlgebra.ringCon K L) u
  subst u
  change d (UniversalEnvelopingAlgebra.mkAlgHom K L t) ∈ T
  induction t using TensorAlgebra.induction with
  | algebraMap c =>
    change d (algebraMap K (adoUEA K L) c) ∈ T
    rwa [Algebra.algebraMap_eq_smul_one, map_smul, hd1, smul_zero]
  | ι x => exact hι x
  | mul x y hx hy =>
    rw [map_mul, hd]
    exact T.add_mem (T.mul_mem_left _ hy) (T.mul_mem_right _ hx)
  | add x y hx hy =>
    rw [map_add, map_add]
    exact T.add_mem hx hy

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoUEA_derivation_preserves_idealPower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoUEA_derivation_preserves_idealPower
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  (d : Module.End K (adoUEA K L))
  (hd : ∀ u v, d (u * v) = u * d v + d u * v)
  (T : Ideal (adoUEA K L)) [T.IsTwoSided]
  (hT : ∀ u, d u ∈ T) (k : ℕ) {u : adoUEA K L} (hu : u ∈ T ^ k) :
  d u ∈ T ^ k := by
  induction k generalizing u with
  | zero =>
    rwa [Submodule.pow_zero, Ideal.one_eq_top]
  | succ k ih =>
    rw [Ideal.IsTwoSided.pow_succ] at hu ⊢
    refine Submodule.mul_induction_on hu ?_ ?_
    · intro x hx y hy
      rw [hd]
      exact Submodule.add_mem _
        (Submodule.mul_mem_mul hx (ih hy))
        (Submodule.mul_mem_mul (hT x) hy)
    · intro x y hx hy
      simpa using Submodule.add_mem _ hx hy

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoQuotient_end_isNilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoQuotient_end_isNilpotent
  {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  (d : Module.End K M) (P : Submodule K M) (hP : P ≤ P.comap d)
  [Module.Finite K (M ⧸ P)]
  (hlocal : ∀ x, ∃ n, (d ^ n) x = 0) :
  IsNilpotent (P.mapQ P d hP) := by
  apply adoEnd_isNilpotent_of_locallyNilpotent
  intro q
  induction q using Quotient.inductionOn' with
  | _ x =>
    obtain ⟨n, hn⟩ := hlocal x
    refine ⟨n, ?_⟩
    rw [← P.mapQ_pow]
    change (Submodule.Quotient.mk ((d ^ n) x) : M ⧸ P) = 0
    rw [hn]
    rfl

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoEnd_isNilpotent_of_restrict_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoEnd_isNilpotent_of_restrict_quotient
  {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  (f : Module.End K M) (P : Submodule K M) (hP : P ≤ P.comap f)
  (hres : IsNilpotent (f.restrict hP))
  (hquot : IsNilpotent (P.mapQ P f hP)) : IsNilpotent f := by
  obtain ⟨a, ha⟩ := hquot
  obtain ⟨b, hb⟩ := hres
  refine ⟨a + b, ?_⟩
  ext m
  have hfam : (f ^ a) m ∈ P := by
    have hz := LinearMap.congr_fun ha (Submodule.Quotient.mk m)
    rw [LinearMap.zero_apply, ← P.mapQ_pow, Submodule.mapQ_apply,
      Submodule.Quotient.mk_eq_zero] at hz
    exact hz
  have hb' := LinearMap.congr_fun hb ⟨(f ^ a) m, hfam⟩
  rw [Module.End.pow_restrict, LinearMap.zero_apply] at hb'
  change (f ^ (a + b)) m = 0
  rw [show a + b = b + a by omega, pow_add, Module.End.mul_apply]
  exact congrArg Subtype.val hb'

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoLieModule_isNilpotent_of_submodule_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoLieModule_isNilpotent_of_submodule_quotient
  {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Finite K M] (P : LieSubmodule K L M)
  (hP : LieModule.IsNilpotent L P)
  (hquot : LieModule.IsNilpotent L (M ⧸ P)) :
  LieModule.IsNilpotent L M := by
  rw [LieModule.isNilpotent_iff_forall' (R := K)] at hP hquot ⊢
  intro x
  let f := LieModule.toEnd K L M x
  let hf : P.toSubmodule ≤ P.toSubmodule.comap f := fun _ hm => P.lie_mem hm
  exact adoEnd_isNilpotent_of_restrict_quotient f P.toSubmodule hf
    (hP x) (hquot x)

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoNilpotent_of_codim_one_extension](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoNilpotent_of_codim_one_extension
  {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Finite K M]
  (A : LieIdeal K L) (h : L)
  (hdecomp : ∀ x : L, ∃ a : A, ∃ c : K, x = a.1 + c • h)
  (hA : LieModule.IsNilpotent A M)
  (hh : IsNilpotent (LieModule.toEnd K L M h)) :
  LieModule.IsNilpotent L M := by
  classical
  by_cases hM : Subsingleton M
  · let _ : Subsingleton M := hM
    infer_instance
  · let _ : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    let F : LieSubmodule K L M := A.lcs M 1
    have hFne : F ≠ ⊤ := by
      intro hF
      obtain ⟨k, hk⟩ := (LieModule.isNilpotent_iff K A M).mp hA
      have hk' : A.lcs M k = ⊥ := by
        rw [← LieSubmodule.toSubmodule_inj, LieIdeal.coe_lcs_eq, hk]
        rfl
      have hall : ∀ n, A.lcs M n = ⊤ := by
        intro n
        induction n with
        | zero => simp [LieIdeal.lcs_zero]
        | succ n ih =>
          rw [show n + 1 = n.succ by rfl, LieIdeal.lcs_succ, ih]
          simpa [F] using hF
      have := (hall k).symm.trans hk'
      exact bot_ne_top this.symm
    have hfin : Module.finrank K F < Module.finrank K M :=
      Submodule.finrank_lt (by
        intro htop
        apply hFne
        rw [← LieSubmodule.toSubmodule_inj]
        exact htop)
    have hAF : LieModule.IsNilpotent A F := by
      rw [LieModule.isNilpotent_iff_forall' (R := K)] at hA ⊢
      intro a
      exact Module.End.isNilpotent.restrict
        (fun _ hm => F.lie_mem hm) (hA a)
    have hhF : IsNilpotent (LieModule.toEnd K L F h) := by
      exact Module.End.isNilpotent.restrict (fun _ hm => F.lie_mem hm) hh
    have hFL : LieModule.IsNilpotent L F :=
      adoNilpotent_of_codim_one_extension A h hdecomp hAF hhF
    have hpres : F.toSubmodule ≤
      F.toSubmodule.comap (LieModule.toEnd K L M h) := fun _ hm => F.lie_mem hm
    have hhquot : IsNilpotent (LieModule.toEnd K L (M ⧸ F) h) := by
      exact Module.End.IsNilpotent.mapQ hpres hh
    have hquot : LieModule.IsNilpotent L (M ⧸ F) := by
      rw [LieModule.isNilpotent_iff_forall' (R := K)]
      intro x
      obtain ⟨a, c, rfl⟩ := hdecomp x
      have ha0 : LieModule.toEnd K L (M ⧸ F) a.1 = 0 := by
        ext q
        induction q using Quotient.inductionOn' with
        | _ m =>
          rw [LinearMap.zero_apply]
          change (Submodule.Quotient.mk ⁅a.1, m⁆ : M ⧸ F) = 0
          rw [Submodule.Quotient.mk_eq_zero]
          change ⁅a.1, m⁆ ∈ F
          rw [show F = ⁅A, (⊤ : LieSubmodule K L M)⁆ from by
            simp [F, LieIdeal.lcs_succ]]
          exact LieSubmodule.lie_mem_lie a.2 (LieSubmodule.mem_top m)
      rw [map_add, map_smul, ha0, zero_add]
      exact hhquot.smul c
    exact adoLieModule_isNilpotent_of_submodule_quotient F hFL hquot
termination_by Module.finrank K M
decreasing_by exact hfin
open LieAlgebra
open scoped TensorProduct

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoCommutator_weightSpace_le_maxTriv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoCommutator_weightSpace_le_maxTriv
  {K G M : Type*} [Field K] [CharZero K] [LieRing G] [LieAlgebra K G]
  [AddCommGroup M] [Module K M] [LieRingModule G M] [LieModule K G M]
  [Module.Finite K M]
  (I : LieIdeal K G) (χ : Module.Dual K I) :
  adoRestrictIdeal (LieModule.weightSpaceOfIsLieTower K M χ) (adoCommutatorIdeal I) ≤
    LieModule.maxTrivSubmodule K (adoCommutatorIdeal I) M := by
  intro m hm
  rw [LieModule.mem_maxTrivSubmodule]
  intro x
  change m ∈ LieModule.weightSpace M χ at hm
  have hm' : ∀ a : I, ⁅a.1, m⁆ = χ a • m := by
    simpa [LieModule.mem_weightSpace] using hm
  have hzm (z : G) : ⁅z, m⁆ ∈ LieModule.weightSpace M χ := by
    exact (LieModule.weightSpaceOfIsLieTower K M χ).lie_mem hm
  have hgenerator (z : G) (a : I) : ⁅⁅z, a.1⁆, m⁆ = 0 := by
    rw [lie_lie, hm' a, lie_smul]
    have ha : ⁅a.1, ⁅z, m⁆⁆ = χ a • ⁅z, m⁆ := by
      exact (LieModule.mem_weightSpace χ _).mp (hzm z) a
    rw [ha, sub_self]
  let f : G →ₗ[K] M :=
    (LinearMap.applyₗ (R := K) m).comp (LieModule.toEnd K G M).toLinearMap
  have hle : (adoCommutatorIdeal I : Submodule K G) ≤ LinearMap.ker f := by
    rw [show (adoCommutatorIdeal I : Submodule K G) =
      Submodule.span K {y | ∃ (z : (⊤ : LieIdeal K G)) (a : I), ⁅z.1, a.1⁆ = y} from
      LieSubmodule.lieIdeal_oper_eq_linear_span (I : LieSubmodule K G G)
        (⊤ : LieIdeal K G)]
    apply Submodule.span_le.mpr
    rintro y ⟨z, a, rfl⟩
    exact hgenerator z.1 a
  have hxker := hle x.2
  change f x.1 = 0 at hxker
  simpa [f, LieModule.toEnd_apply_apply] using hxker

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoCommutator_acts_nilpotently_algClosed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoCommutator_acts_nilpotently_algClosed
  (K G M : Type*) [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing G] [LieAlgebra K G]
  [AddCommGroup M] [Module K M] [LieRingModule G M] [LieModule K G M]
  [Module.Finite K M] (I : LieIdeal K G) [LieAlgebra.IsSolvable I] :
  LieModule.IsNilpotent (adoCommutatorIdeal I) M := by
  classical
  by_cases hM : Subsingleton M
  · let _ : Subsingleton M := hM
    infer_instance
  · let _ : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable K I M
    let W : LieSubmodule K G M := LieModule.weightSpaceOfIsLieTower K M χ
    by_cases hW : W = ⊤
    · have htop : LieModule.maxTrivSubmodule K (adoCommutatorIdeal I) M = ⊤ := by
      rw [← top_le_iff]
      intro m hm
      apply adoCommutator_weightSpace_le_maxTriv I χ
      change m ∈ W
      rw [hW]
      exact LieSubmodule.mem_top m
      let _ : LieModule.IsTrivial (adoCommutatorIdeal I) M :=
        (LieModule.isTrivial_iff_max_triv_eq_top K (adoCommutatorIdeal I) M).mpr htop
      infer_instance
    · have hfin : Module.finrank K (M ⧸ W) < Module.finrank K M := by
      rwa [← Submodule.finrank_quotient_add_finrank W.toSubmodule]
        ((Module.finrank_pos_iff_of_free K W).mpr hχ)
      have hquot : LieModule.IsNilpotent (adoCommutatorIdeal I) (M ⧸ W) :=
        adoCommutator_acts_nilpotently_algClosed K G (M ⧸ W) I
      apply LieModule.nilpotentOfNilpotentQuotient K (adoCommutatorIdeal I) M
        (N := adoRestrictIdeal W (adoCommutatorIdeal I))
      · exact adoCommutator_weightSpace_le_maxTriv (M := M) I χ
      · exact hquot
termination_by Module.finrank K M
decreasing_by exact hfin

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoCommutator_acts_nilpotently](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoCommutator_acts_nilpotently
  {K G M : Type*} [Field K] [CharZero K]
  [LieRing G] [LieAlgebra K G]
  [AddCommGroup M] [Module K M] [LieRingModule G M] [LieModule K G M]
  [Module.Finite K M] (I : LieIdeal K G) [LieAlgebra.IsSolvable I] :
  LieModule.IsNilpotent (adoCommutatorIdeal I) M := by
  set A := AlgebraicClosure (FractionRing K)
  have _i : FaithfulSMul K A := FaithfulSMul.trans K (FractionRing K) A
  let IA : LieIdeal A (A ⊗[K] G) := I.baseChange A
  let _ : LieAlgebra.IsSolvable IA := by
    obtain ⟨k, hk⟩ := LieAlgebra.IsSolvable.solvable K I
    apply LieAlgebra.IsSolvable.mk (R := A)
    rw [LieIdeal.derivedSeries_eq_bot_iff,
      LieAlgebra.derivedSeriesOfIdeal_baseChange]
    · have hk' : LieAlgebra.derivedSeriesOfIdeal K G k I = ⊥ :=
      (I.derivedSeries_eq_bot_iff k).mp hk
      rw [hk', LieSubmodule.baseChange_bot]
  have nilp_ext : LieModule.IsNilpotent
    (adoCommutatorIdeal IA) (A ⊗[K] M) :=
    adoCommutator_acts_nilpotently_algClosed A (A ⊗[K] G) (A ⊗[K] M) IA
  rw [LieModule.isNilpotent_iff_forall' (R := K)]
  rw [LieModule.isNilpotent_iff_forall' (R := A)] at nilp_ext
  intro ⟨x, hx⟩
  have hx_ext : 1 ⊗ₜ[K] x ∈ adoCommutatorIdeal IA := by
    have hIA : adoCommutatorIdeal IA = (adoCommutatorIdeal I).baseChange A := by
      dsimp [IA, adoCommutatorIdeal]
      rw [LieSubmodule.lie_baseChange, LieSubmodule.baseChange_top]
    rw [hIA]
    exact LieSubmodule.tmul_mem_baseChange_of_mem 1 hx
  have hbc_inj : Function.Injective (Module.End.baseChangeHom K A M) :=
    LinearMap.baseChangeHom_injective K M A
  have aux : (LieModule.toEnd K (adoCommutatorIdeal I) M ⟨x, hx⟩).baseChangeHom K A M =
    (LieModule.toEnd K G M x).baseChange A := rfl
  rw [← IsNilpotent.map_iff hbc_inj, aux, ← LieModule.toEnd_baseChange]
  exact nilp_ext ⟨_, hx_ext⟩

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoCommutator_isNilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoCommutator_isNilpotent
  {K G : Type*} [Field K] [CharZero K]
  [LieRing G] [LieAlgebra K G] [Module.Finite K G]
  (I : LieIdeal K G) [LieAlgebra.IsSolvable I] :
  LieRing.IsNilpotent (↑(⁅(⊤ : LieIdeal K G), I⁆ : LieIdeal K G)) := by
  rw [LieAlgebra.isNilpotent_iff_forall (R := K)]
  intro x
  apply LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad
    (adoCommutatorIdeal I : LieSubalgebra K G)
  exact (LieModule.isNilpotent_iff_forall' (R := K)).mp
    (adoCommutator_acts_nilpotently (M := G) I) x

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoAdd_center_isNilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoAdd_center_isNilpotent
  {K G : Type*} [Field K] [LieRing G] [LieAlgebra K G]
  (J : LieIdeal K G) [LieRing.IsNilpotent J] :
  LieRing.IsNilpotent (J + LieAlgebra.center K G : LieIdeal K G) := by
  let B : LieIdeal K G := J + LieAlgebra.center K G
  let C : LieIdeal K B := (LieAlgebra.center K G).comap B.incl
  have hC : C ≤ LieAlgebra.center K B := by
    intro z hz
    rw [LieModule.mem_maxTrivSubmodule]
    intro b
    apply Subtype.ext
    change ⁅(b.1 : G), (z.1 : G)⁆ = 0
    have hzG : (z.1 : G) ∈ LieAlgebra.center K G := hz
    exact (LieModule.mem_maxTrivSubmodule K G G (z.1 : G)).mp hzG b.1
  apply LieAlgebra.nilpotent_of_nilpotent_quotient hC
  let f : J →ₗ⁅K⁆ B ⧸ C :=
    (adoQuotientLieHom C).comp (LieIdeal.inclusion (show J ≤ B from le_sup_left))
  refine Function.Surjective.lieAlgebra_isNilpotent (f := f) ?_
  intro q
  induction q using Quotient.inductionOn' with
  | _ b =>
    have hb : (b.1 : G) ∈ J.toSubmodule ⊔ (LieAlgebra.center K G).toSubmodule := b.2
    obtain ⟨j, hj, z, hz, hjz⟩ := Submodule.mem_sup.mp hb
    refine ⟨⟨j, hj⟩, ?_⟩
    apply (Submodule.Quotient.eq C.toSubmodule).mpr
    have hjB : j ∈ B := Submodule.mem_sup_left hj
    let jb : B := ⟨j, hjB⟩
    change jb - b ∈ C
    change (j - b.1 : G) ∈ LieAlgebra.center K G
    rw [← hjz]
    simpa using (LieAlgebra.center K G).neg_mem hz

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[ado_transport_fin_nilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma ado_transport_fin_nilpotent
  {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [Module.Finite K V]
  (ρ : L →ₗ⁅K⁆ Module.End K V) (hρ : Function.Injective ρ)
  (hnil : ∀ x, IsNilpotent (ρ x)) :
  ∃ (n : ℕ) (ρ' : L →ₗ⁅K⁆ Module.End K (Fin n → K)),
    Function.Injective ρ' ∧ ∀ x, IsNilpotent (ρ' x) := by
  let _ : Module.Free K V := Module.Free.of_divisionRing K V
  let e := (Module.finBasis K V).equivFun
  refine ⟨Module.finrank K V, e.lieConj.comp ρ,
    e.lieConj.injective.comp hρ, ?_⟩
  intro x
  obtain ⟨k, hk⟩ := hnil x
  refine ⟨k, ?_⟩
  change (e.conjAlgEquiv K (ρ x)) ^ k = 0
  rw [← map_pow, hk, map_zero]

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[ado_transport_fin_nilpotent_on](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma ado_transport_fin_nilpotent_on
  {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [Module.Finite K V]
  (N : LieIdeal K L)
  (ρ : L →ₗ⁅K⁆ Module.End K V) (hρ : Function.Injective ρ)
  (hnil : ∀ x : N, IsNilpotent (ρ x.1)) :
  ∃ (n : ℕ) (ρ' : L →ₗ⁅K⁆ Module.End K (Fin n → K)),
    Function.Injective ρ' ∧ ∀ x : N, IsNilpotent (ρ' x.1) := by
  let _ : Module.Free K V := Module.Free.of_divisionRing K V
  let e := (Module.finBasis K V).equivFun
  refine ⟨Module.finrank K V, e.lieConj.comp ρ,
    e.lieConj.injective.comp hρ, ?_⟩
  intro x
  obtain ⟨k, hk⟩ := hnil x
  refine ⟨k, ?_⟩
  change (e.conjAlgEquiv K (ρ x.1)) ^ k = 0
  rw [← map_pow, hk, map_zero]

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoDirectSum_isNilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoDirectSum_isNilpotent
  {K L V W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (ρ : L →ₗ⁅K⁆ Module.End K V) (σ : L →ₗ⁅K⁆ Module.End K W)
  {x : L} (hρ : IsNilpotent (ρ x)) (hσ : IsNilpotent (σ x)) :
  IsNilpotent (adoDirectSum ρ σ x) := by
  obtain ⟨a, ha⟩ := hρ
  obtain ⟨b, hb⟩ := hσ
  refine ⟨a + b, ?_⟩
  have ha' : ρ x ^ (a + b) = 0 := by
    rw [pow_add, ha, zero_mul]
  have hb' : σ x ^ (a + b) = 0 := by
    rw [pow_add, hb, mul_zero]
  change ((LinearMap.prodMapAlgHom K V W) (ρ x, σ x)) ^ (a + b) = 0
  rw [← map_pow]
  have hp : (ρ x, σ x) ^ (a + b) = 0 := by
    ext <;> simp [ha', hb']
  rw [hp, map_zero]

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoLine_isLieAbelian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoLine_isLieAbelian
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] (h : L) :
  IsLieAbelian (adoLineSubalgebra (K := K) h) := by
  constructor
  intro x y
  apply Subtype.ext
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.2
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp y.2
  change ⁅(x : L), (y : L)⁆ = 0
  rw [← ha, ← hb]
  simp

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoCoatom_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoCoatom_decomp
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  (A : LieIdeal K L) (hA : IsCoatom A.toSubmodule) (h : L) (hh : h ∉ A) :
  ∀ x : L, ∃ a : A, ∃ c : K, x = a.1 + c • h := by
  intro x
  have hc : IsCompl A.toSubmodule (K ∙ h) :=
    Submodule.isCompl_span_singleton_of_isCoatom_of_notMem hA hh
  obtain ⟨a, z, ha, hz, rfl⟩ :=
    Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint x
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨⟨a, ha⟩, c, rfl⟩

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoSemidirectRepresentation_preserves_ideal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoSemidirectRepresentation_preserves_ideal
  {K I H : Type*} [Field K] [LieRing I] [LieAlgebra K I]
  [LieRing H] [LieAlgebra K H] (ψ : H →ₗ⁅K⁆ LieDerivation K I I)
  (Q : Ideal (adoUEA K I)) [Q.IsTwoSided]
  (hQ : ∀ h u, u ∈ Q → adoExtendDerivation (ψ h) u ∈ Q) (x : I ⋊⁅ψ⁆ H) :
  (Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K ≤
    ((Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K).comap
      (adoSemidirectRepresentation ψ x) := by
  intro u hu
  change UniversalEnvelopingAlgebra.ι K x.left * u +
    adoExtendDerivation (ψ x.right) u ∈ Q
  exact Q.add_mem (Q.mul_mem_left _ hu) (hQ x.right u hu)

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoSemidirectQuotient_faithful_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoSemidirectQuotient_faithful_left
  {K I H V : Type*} [Field K] [LieRing I] [LieAlgebra K I]
  [LieRing H] [LieAlgebra K H]
  [AddCommGroup V] [Module K V]
  (ψ : H →ₗ⁅K⁆ LieDerivation K I I)
  (ρ : I →ₗ⁅K⁆ Module.End K V) (hρ : Function.Injective ρ)
  (Q : Ideal (adoUEA K I)) [Q.IsTwoSided]
  (hQker :
    (Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K ≤
      LinearMap.ker (UniversalEnvelopingAlgebra.lift K ρ).toLinearMap)
  (hQ : ∀ h u, u ∈ Q → adoExtendDerivation (ψ h) u ∈ Q)
  (a : I)
  (ha : adoQuotientRepresentation (adoSemidirectRepresentation ψ)
    ((Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K)
    (adoSemidirectRepresentation_preserves_ideal ψ Q hQ) ⟨a, 0⟩ = 0) :
  a = 0 := by
  let qK := (Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K
  have ha1 := LinearMap.congr_fun ha (Submodule.Quotient.mk (1 : adoUEA K I))
  have hDz : adoExtendDerivation (ψ (0 : H)) = 0 := by
    change adoExtendDerivationHom (ψ 0) = 0
    rw [map_zero, map_zero]
  have hrep : adoSemidirectRepresentation ψ (⟨a, 0⟩ : I ⋊⁅ψ⁆ H)
    (1 : adoUEA K I) = UniversalEnvelopingAlgebra.ι K a := by
    change UniversalEnvelopingAlgebra.ι K a * 1 +
      adoExtendDerivation (ψ 0) 1 = _
    rw [hDz]
    simp
  have hiota : UniversalEnvelopingAlgebra.ι K a ∈ Q := by
    rw [LinearMap.zero_apply] at ha1
    change (Submodule.Quotient.mk
      (adoSemidirectRepresentation ψ (⟨a, 0⟩ : I ⋊⁅ψ⁆ H) 1) :
        adoUEA K I ⧸ qK) = 0 at ha1
    rw [hrep] at ha1
    rwa [Submodule.Quotient.mk_eq_zero] at ha1
  have hzero := hQker hiota
  rw [LinearMap.mem_ker] at hzero
  have hι : UniversalEnvelopingAlgebra.lift K ρ
    (UniversalEnvelopingAlgebra.ι K a) = ρ a :=
    UniversalEnvelopingAlgebra.lift_ι_apply K ρ a
  change UniversalEnvelopingAlgebra.lift K ρ
    (UniversalEnvelopingAlgebra.ι K a) = 0 at hzero
  rw [hι] at hzero
  exact hρ (hzero.trans (map_zero ρ).symm)

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoQuotient_end_isNilpotent_of_pow_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoQuotient_end_isNilpotent_of_pow_mem
  {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  (d : Module.End K M) (P : Submodule K M) (hP : P ≤ P.comap d)
  (k : ℕ) (hk : ∀ x, (d ^ k) x ∈ P) :
  IsNilpotent (P.mapQ P d hP) := by
  refine ⟨k, ?_⟩
  ext x
  rw [← P.mapQ_pow]
  change (Submodule.Quotient.mk ((d ^ k) x) : M ⧸ P) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact hk x

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoSemidirectQuotient_left_isNilpotent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoSemidirectQuotient_left_isNilpotent
  {K I H : Type*} [Field K] [LieRing I] [LieAlgebra K I]
  [LieRing H] [LieAlgebra K H] (ψ : H →ₗ⁅K⁆ LieDerivation K I I)
  (Q : Ideal (adoUEA K I)) [Q.IsTwoSided]
  (hQ : ∀ h u, u ∈ Q → adoExtendDerivation (ψ h) u ∈ Q)
  (a : I) (k : ℕ) (hpow : (UniversalEnvelopingAlgebra.ι K a) ^ k ∈ Q) :
  IsNilpotent
    (adoQuotientRepresentation (adoSemidirectRepresentation ψ)
      ((Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K)
      (adoSemidirectRepresentation_preserves_ideal ψ Q hQ) ⟨a, 0⟩) := by
  let qK := (Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K
  let d : Module.End K (adoUEA K I) :=
    Algebra.lmul K (adoUEA K I) (UniversalEnvelopingAlgebra.ι K a)
  have hdQ : qK ≤ qK.comap d := by
    intro u hu
    exact Q.mul_mem_left _ hu
  have hdk : ∀ u, (d ^ k) u ∈ qK := by
    intro u
    change ((Algebra.lmul K (adoUEA K I)
      (UniversalEnvelopingAlgebra.ι K a)) ^ k) u ∈ Q
    rw [← map_pow]
    exact Q.mul_mem_right u hpow
  have hnil := adoQuotient_end_isNilpotent_of_pow_mem d qK hdQ k hdk
  have hDz : adoExtendDerivation (ψ (0 : H)) = 0 := by
    change adoExtendDerivationHom (ψ 0) = 0
    rw [map_zero, map_zero]
  have hrep : adoSemidirectRepresentation ψ (⟨a, 0⟩ : I ⋊⁅ψ⁆ H) = d := by
    ext u
    change UniversalEnvelopingAlgebra.ι K a * u +
      adoExtendDerivation (ψ 0) u = UniversalEnvelopingAlgebra.ι K a * u
    rw [hDz]
    simp
  have hmap : qK.mapQ qK
    (adoSemidirectRepresentation ψ (⟨a, 0⟩ : I ⋊⁅ψ⁆ H))
    (adoSemidirectRepresentation_preserves_ideal ψ Q hQ ⟨a, 0⟩) =
    qK.mapQ qK d hdQ := by
    ext u
    change (Submodule.Quotient.mk
      (adoSemidirectRepresentation ψ (⟨a, 0⟩ : I ⋊⁅ψ⁆ H) u) :
        adoUEA K I ⧸ qK) = Submodule.Quotient.mk (d u)
    rw [hrep]
  change IsNilpotent (qK.mapQ qK
    (adoSemidirectRepresentation ψ (⟨a, 0⟩ : I ⋊⁅ψ⁆ H))
    (adoSemidirectRepresentation_preserves_ideal ψ Q hQ ⟨a, 0⟩))
  rwa [hmap]

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoNilpotent_exists_coatom](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoNilpotent_exists_coatom
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [Module.Finite K L] [LieRing.IsNilpotent L]
  (hab : ¬ IsLieAbelian L) :
  ∃ (A : LieIdeal K L), IsCoatom A.toSubmodule ∧
    (LieAlgebra.derivedSeries K L 1 : Submodule K L) ≤ A.toSubmodule ∧
    ∃ h : L, h ∉ A := by
  have hnsub : ¬ Subsingleton L := by
    intro hsub
    apply hab
    let _ : Subsingleton L := hsub
    infer_instance
  let _ : Nontrivial L := not_subsingleton_iff_nontrivial.mp hnsub
  have hder := LieAlgebra.derivedSeries_lt_top_of_solvable K L
  obtain htop | ⟨A, hA, hAL⟩ :=
    eq_top_or_exists_le_coatom (LieAlgebra.derivedSeries K L 1).toSubmodule
  · apply (hder.ne ?_).elim
    rwa [← LieSubmodule.toSubmodule_inj]
  lift A to LieIdeal K L
  · intro x y hy
    exact hAL (LieSubmodule.lie_mem_lie
      (LieSubmodule.mem_top x) (LieSubmodule.mem_top y))
  obtain ⟨h, -, hh⟩ := SetLike.exists_of_lt hA.lt_top
  exact ⟨A, hA, hAL, h, hh⟩

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoCoatom_nontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoCoatom_nontrivial
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  (A : LieIdeal K L)
  (hder : (LieAlgebra.derivedSeries K L 1 : Submodule K L) ≤ A.toSubmodule)
  (hab : ¬ IsLieAbelian L) : Nontrivial A := by
  have hxy : ∃ x y : L, ⁅x, y⁆ ≠ 0 := by
    by_contra h
    apply hab
    constructor
    intro x y
    by_contra hxy
    exact h ⟨x, y, hxy⟩
  obtain ⟨x, y, hxy⟩ := hxy
  let a : A := ⟨⁅x, y⁆, hder (LieSubmodule.lie_mem_lie
    (LieSubmodule.mem_top x) (LieSubmodule.mem_top y))⟩
  exact ⟨⟨a, 0, fun ha => hxy (congrArg Subtype.val ha)⟩⟩

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoAeval_monic_mem_modWords](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoAeval_monic_mem_modWords
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  {d : ℕ} (Q : Ideal (adoUEA K L)) [Q.IsTwoSided]
  (b : Module.Basis (Fin d) K L) (i : Fin d) (p : Polynomial K) (hp : p.Monic)
  (hrel : Polynomial.aeval (UniversalEnvelopingAlgebra.ι K (b i)) p ∈ Q) :
  (UniversalEnvelopingAlgebra.ι K (b i)) ^ p.natDegree ∈
    adoModWords Q b p.natDegree := by
  let x := UniversalEnvelopingAlgebra.ι K (b i)
  let n := p.natDegree
  change x ^ n ∈ adoModWords Q b n
  let r := ∑ j ∈ Finset.range n,
    Polynomial.C (p.coeff j) * Polynomial.X ^ j
  have hlow : Polynomial.aeval x r ∈
    Submodule.span K (adoWordsLt b n) := by
    dsimp [r]
    rw [map_sum]
    apply Submodule.sum_mem
    intro j hj
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    change p.coeff j • x ^ j ∈ Submodule.span K (adoWordsLt b n)
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨List.replicate j i, by simpa using (Finset.mem_range.mp hj), ?_⟩
    simp [x, adoWord]
  have hpas : p = Polynomial.X ^ n + r := by
    simpa [n, r] using hp.as_sum
  have heval : Polynomial.aeval x p =
    x ^ n + Polynomial.aeval x r := by
    rw [hpas, map_add, map_pow, Polynomial.aeval_X]
  have hx : x ^ n = Polynomial.aeval x p - Polynomial.aeval x r := by
    rw [heval]
    abel
  rw [hx]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left hrel)
    (Submodule.mem_sup_right hlow)

end MathlibExt.Algebra.Lie.LandmarkWanted

namespace MathlibExt.Algebra.Lie.LandmarkWanted

/--
[adoIdeal_exists_coatom](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma adoIdeal_exists_coatom
  {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  (N : LieIdeal K L)
  (hderived : (LieAlgebra.derivedSeries K L 1 : Submodule K L) ≤ N.toSubmodule)
  (hN : N ≠ ⊤) :
  ∃ (A : LieIdeal K L), IsCoatom A.toSubmodule ∧ N ≤ A ∧
    ∃ h : L, h ∉ A := by
  have hN' : N.toSubmodule ≠ ⊤ := by
    intro h
    apply hN
    rwa [← LieSubmodule.toSubmodule_inj]
  obtain htop | ⟨A, hA, hNA⟩ := eq_top_or_exists_le_coatom N.toSubmodule
  · exact (hN' htop).elim
  lift A to LieIdeal K L
  · intro x y hy
    exact hNA (hderived (LieSubmodule.lie_mem_lie
      (LieSubmodule.mem_top x) (LieSubmodule.mem_top y)))
  obtain ⟨h, -, hh⟩ := SetLike.exists_of_lt hA.lt_top
  exact ⟨A, hA, hNA, h, hh⟩

end MathlibExt.Algebra.Lie.LandmarkWanted

/--
[ado](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean)
-/
@[path]
private lemma ado_eq
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L] :
-- imply
  ∃ (n : ℕ) (ρ : L →ₗ⁅K⁆ Module.End K (Fin n → K)),
    Function.Injective ρ := by
-- proof
  apply MathlibExt.Algebra.Lie.LandmarkWanted.ado


-- created on 2026-10-20
-- updated on 2026-10-23
