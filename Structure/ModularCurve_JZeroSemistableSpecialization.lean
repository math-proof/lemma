import Lemma.AlgebraicCurve.GluedPic0
import Lemma.AlgebraicCurve.GluedPic0Functoriality
import Instance.ModularCurve_ArithmeticGalois
import Def.ModularCurve_JqCoeff
import Structure.HeckeGalois_EichlerShimura
import Def.ModularCurve_ComponentGroup
import Instance.ModularCurve_JZeroSemistableSpecialization

noncomputable section

namespace ModularCurve

open AlgebraicCurve IsLocalRing

local notation "Qbar" => AlgebraicClosure ℚ

section Generic

def PrimeToTorsion (q : ℕ) {M : Type*} [AddMonoid M] (x : M) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ¬ q ∣ n ∧ n • x = 0

namespace PrimeToTorsion

variable {q : ℕ} {M M' : Type*}


end PrimeToTorsion

def smulInvariants {G : Type*} [Group G] (I : Subgroup G) (M : Type*) [AddCommGroup M]
    [DistribMulAction G M] : AddSubgroup M where
  carrier := {x | ∀ σ ∈ I, σ • x = x}
  zero_mem' := fun σ _ => smul_zero σ
  add_mem' := fun {x y} hx hy σ hσ => by rw [smul_add, hx σ hσ, hy σ hσ]
  neg_mem' := fun {x} hx σ hσ => by rw [smul_neg, hx σ hσ]


end Generic

section Inertia

variable (A : ValuationSubring Qbar) (M : ℕ)

def inertiaInvariants : AddSubgroup (JZero M) :=
  smulInvariants (A.inertiaSubgroupIn ℚ) (JZero M)

variable {A M}


end Inertia

section Semistable

variable (A : ValuationSubring Qbar) (N q : ℕ) (hq : q.Prime) [NeZero N]

variable [Module HeckeAlg (JZero (N * q))] [Module HeckeAlg (JZero N)]
  [Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

structure JZeroSemistableSpecialization where

  nodes : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) ×
    Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))

  nodes_rational : ∀ s ∈ nodes,
    Function.Surjective (algebraMap (ResidueField A) s.1.ResidueField) ∧
      Function.Surjective (algebraMap (ResidueField A) s.2.ResidueField)

  frob : SemilinearAut (ResidueField A) (modularFunctionFieldC (ResidueField A) N)

  frob_nodeStable : SemilinearAut.IsNodeStable nodes frob

  baseAut_frob : ∀ a : ResidueField A, SemilinearAut.baseAut frob a = a ^ q

  nodePerm_nodePerm : ∀ s : ↥nodes, SemilinearAut.nodePerm nodes frob frob_nodeStable
    (SemilinearAut.nodePerm nodes frob frob_nodeStable s) = s

  width : ↥nodes → ℕ

  comp : ↥(inertiaInvariants A (N * q)) →+ componentGroup width

  comp_heckeGen : ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N * q →
    ∀ (x : ↥(inertiaInvariants A (N * q)))
      (hx : heckeGen ℓ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
      comp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩ = (((ℓ : ℕ) : ℤ) + 1) • comp x

  comp_hecke_of_comp_eq_zero : ∀ (T : HeckeAlg) (x : ↥(inertiaInvariants A (N * q)))
      (hx : T • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
      comp x = 0 → comp ⟨T • (x : JZero (N * q)), hx⟩ = 0

  comp_frob_of_comp_eq_zero : ∀ φ : Qbar ≃ₐ[ℚ] Qbar, A.IsFrobeniusAt φ q →
    ∀ (x : ↥(inertiaInvariants A (N * q)))
      (hx : φ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
      comp x = 0 → comp ⟨φ • (x : JZero (N * q)), hx⟩ = 0

  sp : ↥(inertiaInvariants A (N * q)) →+
    GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N) nodes

  toPic0Pair_sp_heckeGen : ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N * q →
    ∀ (x : ↥(inertiaInvariants A (N * q)))
      (hx : heckeGen ℓ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
      comp x = 0 → GluedPic0.toPic0Pair nodes (sp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩) =
        heckeGen ℓ • GluedPic0.toPic0Pair nodes (sp x)

  toPic0Pair_sp_eq_zero : ∀ (T : HeckeAlg) (x : ↥(inertiaInvariants A (N * q)))
      (hx : T • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
      comp x = 0 → GluedPic0.toPic0Pair nodes (sp x) = 0 →
        GluedPic0.toPic0Pair nodes (sp ⟨T • (x : JZero (N * q)), hx⟩) = 0

  sp_frob : ∀ φ : Qbar ≃ₐ[ℚ] Qbar, A.IsFrobeniusAt φ q →
    ∀ (x : ↥(inertiaInvariants A (N * q)))
      (hx : φ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
      comp x = 0 → sp ⟨φ • (x : JZero (N * q)), hx⟩ =
        GluedPic0.glueMap nodes frob frob_nodeStable (sp x)

  sp_heckeGen_self : ∀ (x : ↥(inertiaInvariants A (N * q)))
      (hx : heckeGen ⟨q, hq⟩ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
      comp x = 0 → ∀ w : ↥nodes → Additive (ResidueField A)ˣ,
        sp x = GluedPic0.nodeUnit nodes w →
          sp ⟨heckeGen ⟨q, hq⟩ • (x : JZero (N * q)), hx⟩ = GluedPic0.nodeUnit nodes
            (fun t => w ((SemilinearAut.nodePerm nodes frob frob_nodeStable).symm t))

  sp_injective : ∀ x : ↥(inertiaInvariants A (N * q)),
    PrimeToTorsion q (x : JZero (N * q)) → comp x = 0 → sp x = 0 → x = 0

  exists_prime_torsion : ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → IsUnit ((q : ℕ) : HeckeAlg ⧸ 𝔪) →
    ∀ x ∈ heckeTorsion (JZero (N * q)) 𝔪, ∃ p : ℕ, p.Prime ∧ p ≠ q ∧ p • x = 0

  spN : JZero N →+ Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)

  spN_hecke : ∀ (T : HeckeAlg) (y : JZero N), spN (T • y) = T • spN y

  spN_injective : ∀ y : JZero N, PrimeToTorsion q y → spN y = 0 → y = 0

  spN_surjective : ∀ c : Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N),
    PrimeToTorsion q c → ∃ y : JZero N, PrimeToTorsion q y ∧ spN y = c

end Semistable

end ModularCurve

end
