import Mathlib
import sympy.Basic
import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part3
open WeierstrassCurve WeierstrassCurve.Affine in
open WeierstrassCurve.Affine


namespace WeierstrassCurve.Affine

/--
[multiplicationByN_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma multiplicationByN_apply
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
  {n : ℤ}
  {P : W.Point} :
-- imply
  multiplicationByN W n P = n • P :=
-- proof
  rfl

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[mem_torsionSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma mem_torsionSubgroup
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
  {n : ℤ}
  {P : W.Point} :
-- imply
  P ∈ torsionSubgroup W n ↔ n • P = 0 := by
-- proof
  simp [torsionSubgroup, multiplicationByN, AddMonoidHom.mem_ker]

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[IsSupersingular.torsion_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma IsSupersingular.torsion_eq_zero
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
  {p : ℕ}
  [CharP F p]
  [Fact (Nat.Prime p)]
  {P : W.Point}
-- given
  (h : IsSupersingular W p)
  (hP : (p : ℤ) • P = 0) :
-- imply
  P = 0 := by
-- proof
  have : P ∈ torsionSubgroup W (p : ℤ) := by simp [hP]
  rw [h] at this
  exact AddSubgroup.mem_bot.mp this

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[isSupersingular_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma isSupersingular_iff
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
  {p : ℕ}
  [CharP F p]
  [Fact (Nat.Prime p)] :
-- imply
  IsSupersingular W p ↔ ∀ (P : W.Point), (p : ℤ) • P = 0 → P = 0 := by
-- proof
  constructor
  · exact fun h P hP => h.torsion_eq_zero P hP
  · intro h
    rw [IsSupersingular, AddSubgroup.eq_bot_iff_forall]
    intro P hP
    exact h P (by rwa [mem_torsionSubgroup] at hP)
end Isogeny

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[multiplicationByN_comp_hom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma multiplicationByN_comp_hom
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : E₁.Point →+ E₂.Point}
  {n : ℤ} :
-- imply
  (multiplicationByN E₂ n).comp α = α.comp (multiplicationByN E₁ n) := by
-- proof
  ext P
  simp only [AddMonoidHom.comp_apply, multiplicationByN_apply]
  exact (α.map_zsmul P n).symm

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[multiplicationByN_comm_hom_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma multiplicationByN_comm_hom_apply
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : E₁.Point →+ E₂.Point}
  {n : ℤ}
  {P : E₁.Point} :
-- imply
  n • (α P) = α (n • P) :=
-- proof
  (α.map_zsmul P n).symm
/-- A nonzero integer multiple of a (nonzero) isogeny remains a nonzero homomorphism;
expresses the torsion-freeness of `Hom(E₁, E₂)` as a `ℤ`-module. -/
section Lemma66

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[Isogeny.right_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma Isogeny.right_cancel
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {E₀ E₁ E₂ : WeierstrassCurve.Affine F}
  {α β : Isogeny E₁ E₂}
  {γ : Isogeny E₀ E₁}
-- given
  (h : α.toAddMonoidHom.comp γ.toAddMonoidHom = β.toAddMonoidHom.comp γ.toAddMonoidHom) :
-- imply
  α.toAddMonoidHom = β.toAddMonoidHom := by
-- proof
  ext Q
  obtain ⟨P, hP⟩ := γ.surjective Q
  have := DFunLike.congr_fun h P
  simp only [AddMonoidHom.comp_apply] at this
  rwa [hP] at this
/-- An isogeny composed with a nonzero homomorphism is itself nonzero: pre-composition by
an isogeny `δ` reflects nonzeroness of homomorphisms. -/
end WeierstrassCurve.Affine
noncomputable section
open WeierstrassCurve


/--
[EllipticCurve.torsion_prime_char_supersingular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma EllipticCurve.torsion_prime_char_supersingular
  {k : Type*}
  [Field k]
  {E : WeierstrassCurve k}
  [E.IsElliptic]
  {K : Type*}
  [Field K]
  [Algebra k K]
  [IsAlgClosed K]
  {p : ℕ}
  [CharP k p]
  [Fact (Nat.Prime p)]
  {e : ℕ}
-- given
  (he : 0 < e)
  (hss : EllipticCurve.torsionSubgroup k E K (p : ℤ) = ⊥) :
-- imply
  EllipticCurve.torsionSubgroup k E K ((p : ℤ) ^ e) = ⊥ := by
-- proof
  induction e with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    ·
      subst hn
      simpa [pow_one] using hss
    ·
      have ih' : EllipticCurve.torsionSubgroup k E K ((p : ℤ) ^ n) = ⊥ :=
        ih (Nat.pos_of_ne_zero hn)
      rw [AddSubgroup.eq_bot_iff_forall]
      intro P hP
      rw [EllipticCurve.mem_torsionSubgroup] at hP
      have hpP_mem : (p : ℤ) • P ∈ EllipticCurve.torsionSubgroup k E K ((p : ℤ) ^ n) := by
        rw [EllipticCurve.mem_torsionSubgroup, ← mul_smul]
        rwa [show (p : ℤ) ^ n * (p : ℤ) = (p : ℤ) ^ (n + 1) from by ring]
      rw [ih'] at hpP_mem
      rw [AddSubgroup.mem_bot] at hpP_mem
      have hP_mem : P ∈ EllipticCurve.torsionSubgroup k E K (p : ℤ) := by
        rwa [EllipticCurve.mem_torsionSubgroup]
      rw [hss] at hP_mem
      exact AddSubgroup.mem_bot.mp hP_mem
/-- Ordinarity propagates to powers of `p`: if `E[p] ≃ ℤ/pℤ` then `E[pᵉ] ≃ ℤ/pᵉℤ`. -/
end
section Theorem67
open WeierstrassCurve.Affine in
/-- The degree of a composition of isogenies is the product of the degrees:
`deg(ψ ∘ φ) = deg ψ · deg φ`. -/
@[simp] theorem Isogeny.degree_comp {F : Type u} [Field F] [DecidableEq F]
  {E₁ E₂ E₃ : WeierstrassCurve.Affine F}
  (ψ : Isogeny E₂ E₃) (φ : Isogeny E₁ E₂) :
  (Isogeny.comp ψ φ).degree = ψ.degree * φ.degree := rfl

/--
[Isogeny.dual_exists_of_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma Isogeny.dual_exists_of_comp
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ E_mid : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂}
  {β : Isogeny E₁ E_mid}
  {γ : Isogeny E_mid E₂}
-- given
  (hcomp : γ.toAddMonoidHom.comp β.toAddMonoidHom = α.toAddMonoidHom)
  (hdeg : γ.degree * β.degree = α.degree)
  (hβ_dual : ∃ (βd : Isogeny E_mid E₁), βd.toAddMonoidHom.comp β.toAddMonoidHom = multiplicationByN E₁ (β.degree : ℤ))
  (hγ_dual : ∃ (γd : Isogeny E₂ E_mid), γd.toAddMonoidHom.comp γ.toAddMonoidHom = multiplicationByN E_mid (γ.degree : ℤ)) :
-- imply
  ∃ (αd : Isogeny E₂ E₁), αd.toAddMonoidHom.comp α.toAddMonoidHom = multiplicationByN E₁ (α.degree : ℤ) := by
-- proof
  obtain ⟨βd, hβd⟩ := hβ_dual
  obtain ⟨γd, hγd⟩ := hγ_dual
  refine ⟨Isogeny.comp βd γd, ?_⟩
  have key : ∀ P : E₁.Point,
    βd.toAddMonoidHom (γd.toAddMonoidHom (γ.toAddMonoidHom (β.toAddMonoidHom P))) =
      (↑α.degree : ℤ) • P := by
    intro P
    have h1 : γd.toAddMonoidHom (γ.toAddMonoidHom (β.toAddMonoidHom P)) =
      (γ.degree : ℤ) • (β.toAddMonoidHom P) := by
      have := DFunLike.congr_fun hγd (β.toAddMonoidHom P)
      simp only [AddMonoidHom.comp_apply, multiplicationByN_apply] at this
      exact this
    rw [h1]
    rw [map_zsmul βd.toAddMonoidHom]
    have h2 : βd.toAddMonoidHom (β.toAddMonoidHom P) = (β.degree : ℤ) • P := by
      have := DFunLike.congr_fun hβd P
      simp only [AddMonoidHom.comp_apply, multiplicationByN_apply] at this
      exact this
    rw [h2, ← mul_smul]
    congr 1
    exact_mod_cast hdeg
  ext P
  simp only [AddMonoidHom.comp_apply, multiplicationByN_apply]
  have hαP : α.toAddMonoidHom P = γ.toAddMonoidHom (β.toAddMonoidHom P) := by
    have := DFunLike.congr_fun hcomp P
    simp only [AddMonoidHom.comp_apply] at this
    exact this.symm
  show βd.toAddMonoidHom (γd.toAddMonoidHom (α.toAddMonoidHom P)) = _
  rw [hαP]
  exact key P

/--
[Isogeny.factor_through_kernel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma Isogeny.factor_through_kernel
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ E₃ : WeierstrassCurve.Affine F}
  {φ : Isogeny E₁ E₂}
  {ψ : Isogeny E₁ E₃}
-- given
  (hker : φ.toAddMonoidHom.ker ≤ ψ.toAddMonoidHom.ker) :
-- imply
  ∃ (lam : Isogeny E₂ E₃), lam.toAddMonoidHom.comp φ.toAddMonoidHom = ψ.toAddMonoidHom := by
-- proof
  let lamHom : E₂.Point →+ E₃.Point :=
    φ.toAddMonoidHom.liftOfSurjective φ.surjective ⟨ψ.toAddMonoidHom, hker⟩
  have hcomp : lamHom.comp φ.toAddMonoidHom = ψ.toAddMonoidHom := by simp [lamHom]
  have hlam_surj : Function.Surjective lamHom := by
    intro z
    obtain ⟨x, hx⟩ := ψ.surjective z
    exact ⟨φ.toAddMonoidHom x, by simp [lamHom, hx]⟩
  exact ⟨⟨lamHom, hlam_surj, ψ.degree, ψ.degree_pos⟩, hcomp⟩
open WeierstrassCurve.Affine in
/-- Existence of the dual for a prime-degree isogeny: when `deg α` is prime, the dual
exists, by factoring `[deg α]` through `α`. -/
end Theorem67

/--
[Isogeny.dual_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma Isogeny.dual_unique
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂}
  {αd₁ αd₂ : Isogeny E₂ E₁}
-- given
  (h₁ : αd₁.toAddMonoidHom.comp α.toAddMonoidHom = WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ))
  (h₂ : αd₂.toAddMonoidHom.comp α.toAddMonoidHom = WeierstrassCurve.Affine.multiplicationByN E₁ (α.degree : ℤ)) :
-- imply
  αd₁.toAddMonoidHom = αd₂.toAddMonoidHom :=
-- proof
  WeierstrassCurve.Affine.Isogeny.right_cancel αd₁ αd₂ α (h₁.trans h₂.symm)

/--
[Isogeny.ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma Isogeny.ext
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α β : Isogeny E₁ E₂}
-- given
  (h_hom : α.toAddMonoidHom = β.toAddMonoidHom)
  (h_deg : α.degree = β.degree) :
-- imply
  α = β := by
-- proof
  cases α; cases β
  simp only [Isogeny.mk.injEq]
  exact ⟨h_hom, h_deg⟩
/-- Any isogeny `β` satisfying the dual equation `β ∘ α = [deg α]` automatically has
`deg β = deg α` — using `deg(β ∘ α) = (deg α)²`. -/
section Lemma610
open WeierstrassCurve.Affine
/-- The dual isogeny has the same degree as the original (part of Lemma 6.10). -/
end Lemma610
section Lemma611
open WeierstrassCurve.Affine
/-- Lemma 6.11: the dual is additive — `(α + β)̂ = α̂ + β̂` for `α, β ∈ Hom(E₁, E₂)`. -/
end Lemma611
section Lemma612
open WeierstrassCurve.Affine
/-- Lemma 6.12: the dual of a composition is the reversed composition of duals,
`(α ∘ β)̂ = β̂ ∘ α̂`. -/
end Lemma612
section Definition613
open WeierstrassCurve.Affine
variable {F : Type u} [Field F] [DecidableEq F]
variable (E : WeierstrassCurve.Affine F)

/--
[intToEndRingHom_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma intToEndRingHom_apply
  {E}
  {n : ℤ}
  {P : E.Point} :
-- imply
  (intToEndRingHom (E := E) n) P = n • P := by
-- proof
  simp [intToEndRingHom]

/--
[intToEndRingHom_eq_multiplicationByN](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma intToEndRingHom_eq_multiplicationByN
  {E}
  {n : ℤ} :
-- imply
  intToEndRingHom (E := E) n = multiplicationByN E n :=
-- proof
  rfl

/--
[intCast_comm_endomorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma intCast_comm_endomorphism
  {E}
  {n : ℤ}
  {α : EndRing E} :
-- imply
  (n : EndRing E) * α = α * (n : EndRing E) := by
-- proof
  apply AddMonoidHom.ext
  intro P
  show (n : EndRing E) (α P) = α ((n : EndRing E) P)
  simp only [AddMonoid.End.intCast_def]
  exact (α.map_zsmul P n).symm

/--
[EndRing.mul_apply'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma EndRing.mul_apply'
  {E}
  {α β : EndRing E}
  {P : E.Point} :
-- imply
  (α * β) P = α (β P) :=
-- proof
  rfl

/--
[EndRing.add_apply'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma EndRing.add_apply'
  {E}
  {α β : EndRing E}
  {P : E.Point} :
-- imply
  (α + β) P = α P + β P :=
-- proof
  rfl

/--
[EndRing.one_apply'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma EndRing.one_apply'
  {E}
  {P : E.Point} :
-- imply
  (1 : EndRing E) P = P :=
-- proof
  rfl

/--
[EndRing.zero_apply'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
lemma EndRing.zero_apply'
  {E}
  {P : E.Point} :
-- imply
  (0 : EndRing E) P = 0 :=
-- proof
  rfl
end Definition613
section Lemma616
open WeierstrassCurve.Affine
variable {F : Type u} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F}
/-- Auxiliary form of Lemma 6.16: if `oneMinusAlpha = [1] - α` as homs, then its dual
equals `[1] - α̂`. Used to relate the duals of `α` and `1 - α`. -/
end Lemma616
section Definition617
open WeierstrassCurve.Affine
variable {F : Type u} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F}

/--
[map_mem_torsionSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
private lemma map_mem_torsionSubgroup_eq
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {W₁ W₂ : WeierstrassCurve.Affine F}
  {φ : W₁.Point →+ W₂.Point}
  {n : ℤ}
  {P : W₁.Point}
-- given
  (hP : P ∈ torsionSubgroup W₁ n) :
-- imply
  φ P ∈ torsionSubgroup W₂ n := by
-- proof
  apply WeierstrassCurve.Affine.map_mem_torsionSubgroup φ n P hP

/--
[EllipticCurve.mem_torsionSubgroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
private lemma mem_torsionSubgroup_eq_2
  {k : Type*}
  [Field k]
  {E : WeierstrassCurve k}
  [E.IsElliptic]
  {K : Type*}
  [Field K]
  [Algebra k K]
  {n : ℤ}
  {P : (E.map (algebraMap k K)).toProjective.Point} :
-- imply
  P ∈ EllipticCurve.torsionSubgroup k E K n ↔ n • P = 0 := by
-- proof
  apply EllipticCurve.mem_torsionSubgroup k E K n P

/--
[Isogeny.degree_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean)
-/
@[path]
private lemma degree_comp_eq
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ E₃ : WeierstrassCurve.Affine F}
  {ψ : Isogeny E₂ E₃}
  {φ : Isogeny E₁ E₂} :
-- imply
  (Isogeny.comp ψ φ).degree = ψ.degree * φ.degree := by
-- proof
  apply Isogeny.degree_comp ψ φ


-- created on 2026-10-23
