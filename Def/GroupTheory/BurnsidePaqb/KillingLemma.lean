module
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.RingTheory.Norm.Transitivity
public import Def.GroupTheory.BurnsidePaqb.CentralCharacter.Part3
public import Theorem.Representation.MulCentralScalarFinrankV.eq.Sum_Character
public import Theorem.Complex.In_CycSubfield.of.EqPow_1.Ne_0
public import Instance.GroupTheory.BurnsidePaqb.CyclotomicField


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/KillingLemma.lean -/
/-!
Norm/killing stage of the complete Burnside proof.

Authors: Muse Spark 1.3, @toskua, Avocado
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/KillingLemma.lean`.
-/
namespace BurnsidePaqb

variable {G : Type*} [Group G] [Fintype G]

/-- A characteristic root as an element of the cyclotomic field. -/
noncomputable def conjRootElem (m : ℕ) (hm : m ≠ 0)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G)
    (hmg : ∀ μ ∈ (ρ g).charpoly.roots, μ ^ m = 1)
    (x : { μ : ℂ // μ ∈ (ρ g).charpoly.roots }) : cycSubfield m :=
  ⟨x.1, mem_cycSubfield_of_pow_eq_one m hm x.1 (hmg x.1 x.2)⟩

end BurnsidePaqb
