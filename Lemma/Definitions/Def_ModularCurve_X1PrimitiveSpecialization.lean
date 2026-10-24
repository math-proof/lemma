import Mathlib
import Lemma.Definitions.Def_FLTPrelim_Ramification
import Lemma.Definitions.Def_ModularCurve_X1Diamond
import Lemma.Definitions.Def_EllipticCurve_TateModule

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve CongruenceSubgroup

namespace ModularCurve

section NormFree

def primitiveReps (M₀ q c : ℕ) : Finset ℕ :=
  (Finset.range (M₀ * q ^ c)).filter
    (fun d => Nat.Coprime d (M₀ * q ^ c) ∧ d ≡ 1 [MOD M₀ * q ^ (c - 1)])

theorem mem_primitiveReps {M₀ q c d : ℕ} :
    d ∈ primitiveReps M₀ q c ↔
      d < M₀ * q ^ c ∧ Nat.Coprime d (M₀ * q ^ c) ∧ d ≡ 1 [MOD M₀ * q ^ (c - 1)] := by
  rw [primitiveReps, Finset.mem_filter, Finset.mem_range]

variable (M : ℕ)

def normFreeEnd (S : Finset ℕ) : JOne M →+ JOne M where
  toFun x := S.card • x - ∑ d ∈ S, diamondOneBar M d x
  map_zero' := by simp
  map_add' x y := by
    rw [nsmul_add, Finset.sum_congr rfl fun d _ => map_add (diamondOneBar M d) x y,
      Finset.sum_add_distrib]
    abel

@[simp]
theorem normFreeEnd_apply (S : Finset ℕ) (x : JOne M) :
    normFreeEnd M S x = S.card • x - ∑ d ∈ S, diamondOneBar M d x :=
  rfl

def primitivePart (M₀ q c : ℕ) : AddSubgroup (JOne (M₀ * q ^ c)) :=
  (normFreeEnd (M₀ * q ^ c) (primitiveReps M₀ q c)).range

theorem mem_primitivePart {M₀ q c : ℕ} {y : JOne (M₀ * q ^ c)} :
    y ∈ primitivePart M₀ q c ↔ ∃ x, normFreeEnd (M₀ * q ^ c) (primitiveReps M₀ q c) x = y :=
  AddMonoidHom.mem_range

theorem normFreeEnd_mem_primitivePart {M₀ q c : ℕ} (x : JOne (M₀ * q ^ c)) :
    normFreeEnd (M₀ * q ^ c) (primitiveReps M₀ q c) x ∈ primitivePart M₀ q c :=
  ⟨x, rfl⟩

end NormFree

section Datum

variable (M₀ q c : ℕ) (P : ValuationSubring (AlgebraicClosure ℚ))
variable (k : Type) [Field k] (π : P →+* k)

structure X1PrimitiveSpecialization where

  igusaDiamond : ℕ → (x1FunctionFieldC k (M₀ * q ^ c) ≃ₐ[k] x1FunctionFieldC k (M₀ * q ^ c))

  igusaDiamond_apply_eq : ∀ (d : ℕ) (y y' : LaurentSeries P)
    (hy : coeffMap P.subtype y ∈ x1FunctionFieldBar (M₀ * q ^ c))
    (hy' : coeffMap P.subtype y' ∈ x1FunctionFieldBar (M₀ * q ^ c)),
    diamondAutBar (M₀ * q ^ c) d ⟨coeffMap P.subtype y, hy⟩ = ⟨coeffMap P.subtype y', hy'⟩ →
      ∀ (hk : coeffMap π y ∈ x1FunctionFieldC k (M₀ * q ^ c))
        (hk' : coeffMap π y' ∈ x1FunctionFieldC k (M₀ * q ^ c)),
        igusaDiamond d ⟨coeffMap π y, hk⟩ = ⟨coeffMap π y', hk'⟩

  spInf : primitivePart M₀ q c →+ JOneC (M₀ * q ^ c) k

  spZero : primitivePart M₀ q c →+ JOneC (M₀ * q ^ c) k

  spInf_smul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ (y : primitivePart M₀ q c)
    (h : σ • (y : JOne (M₀ * q ^ c)) ∈ primitivePart M₀ q c), spInf ⟨_, h⟩ = spInf y

  spInf_diamondOneBar : ∀ (d : ℕ) (y : primitivePart M₀ q c)
    (h : diamondOneBar (M₀ * q ^ c) d (y : JOne (M₀ * q ^ c)) ∈ primitivePart M₀ q c),
    spInf ⟨_, h⟩ = SemilinearAut.ofAlgAut (igusaDiamond d) • spInf y

  spZero_diamondOneBar_smul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ u : ℕ, u ≡ 1 [MOD M₀] →
    (∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ c) = 1 → σ ζ = ζ ^ u) →
      ∀ (y : primitivePart M₀ q c)
        (h : diamondOneBar (M₀ * q ^ c) u (σ • (y : JOne (M₀ * q ^ c))) ∈ primitivePart M₀ q c),
        spZero ⟨_, h⟩ = spZero y

  eq_zero_of_forall_eq_zero : ∀ (p : ℕ) [Fact p.Prime], p ≠ q →
    ∀ (y : TateModule p (JOne (M₀ * q ^ c)))
      (h : ∀ n, (y : ℕ → JOne (M₀ * q ^ c)) n ∈ primitivePart M₀ q c),
      (∀ n, spInf ⟨_, h n⟩ = 0) → (∀ n, spZero ⟨_, h n⟩ = 0) → y = 0

end Datum

end ModularCurve

end
