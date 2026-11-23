module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.EllipticCurves.code.Lattice.Part2

public section

open Complex Module ZSpan Set ComplexLattice
open Pointwise


/--
[linearIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean)
-/
public theorem linearIndependent
  {L : ComplexLattice} :
-- imply
  LinearIndependent ℝ ![L.ω₁, L.ω₂] :=
-- proof
  L.indep


variable (L : ComplexLattice)
/--
[ω₁_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean)
-/
public theorem ω₁_mem : L.ω₁ ∈ L.lattice :=
  L.ω₁_mem_lattice


variable (L : ComplexLattice)
/--
[ω₂_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean)
-/
public theorem ω₂_mem : L.ω₂ ∈ L.lattice :=
  L.ω₂_mem_lattice


/--
[finrank_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean)
-/
public theorem finrank_eq_two
  {L : ComplexLattice} :
-- imply
  finrank ℤ L.lattice = 2 :=
-- proof
  L.finrank_lattice


/--
[isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean)
-/
public theorem isClosed
  {L : ComplexLattice} :
-- imply
  IsClosed (L.lattice : Set ℂ) :=
-- proof
  L.isClosed_lattice


/--
[linearIndependent_int](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean)
-/
public theorem linearIndependent_int
  {L : ComplexLattice} :
-- imply
  ∀ (a b : ℤ), a • L.ω₁ + b • L.ω₂ = 0 → a = 0 ∧ b = 0 := by
-- proof
  intro a b h
  have hli := LinearIndependent.pair_iff.mp (linearIndependent (L := L)) (a : ℝ) (b : ℝ)
  rw [Int.cast_smul_eq_zsmul ℝ, Int.cast_smul_eq_zsmul ℝ] at hli
  obtain ⟨ha, hb⟩ := hli h
  exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩


/--
[isHomothetic_refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean)
-/
public theorem isHomothetic_refl
  {L : ComplexLattice} :
-- imply
  IsHomothetic L L :=
-- proof
  ⟨1, one_ne_zero, (one_smul ℂ (L.lattice : Set ℂ)).symm⟩


/--
[isHomothetic_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean)
-/
public theorem isHomothetic_symm
  {L L' : ComplexLattice}
-- given
  (h : IsHomothetic L L') :
-- imply
  IsHomothetic L' L := by
-- proof
  obtain ⟨c, hc, hcL⟩ := h
  exact ⟨c⁻¹, inv_ne_zero hc, by rw [hcL, inv_smul_smul₀ hc]⟩


/--
[isHomothetic_trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean)
-/
public theorem isHomothetic_trans
  {L₁ L₂ L₃ : ComplexLattice}
-- given
  (h₁₂ : IsHomothetic L₁ L₂)
  (h₂₃ : IsHomothetic L₂ L₃) :
-- imply
  IsHomothetic L₁ L₃ := by
-- proof
  obtain ⟨c₁, hc₁, hc₁L⟩ := h₁₂
  obtain ⟨c₂, hc₂, hc₂L⟩ := h₂₃
  exact ⟨c₂ * c₁, mul_ne_zero hc₂ hc₁, by rw [hc₂L, hc₁L, smul_smul]⟩


/--
[isHomothetic_equivalence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean)
-/
public theorem isHomothetic_equivalence :
-- imply
  Equivalence IsHomothetic :=
-- proof
  ⟨fun _ => isHomothetic_refl, isHomothetic_symm, isHomothetic_trans⟩


/--
[discriminantLattice_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean)
-/
public theorem discriminantLattice_def
  {L : ComplexLattice} :
-- imply
  L.discriminantLattice = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 :=
-- proof
  rfl


/--
[jInvariantLattice_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean)
-/
public theorem jInvariantLattice_def
  {L : ComplexLattice} :
-- imply
  L.jInvariantLattice = 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) :=
-- proof
  rfl


/--
[fundamentalParallelogram_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean)
-/
public theorem fundamentalParallelogram_zero
  {L : ComplexLattice} :
-- imply
  fundamentalParallelogram L 0 = ZSpan.fundamentalDomain L.basis := by
-- proof
  simp [fundamentalParallelogram]


/--
[basis_repr_omega](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean)
-/
public theorem basis_repr_omega
  {L : ComplexLattice}
  {t₁ t₂ : ℝ}
  {i : Fin 2} :
-- imply
  L.basis.repr (t₁ • L.ω₁ + t₂ • L.ω₂) i = ![t₁, t₂] i := by
-- proof
  rw [show t₁ • L.ω₁ + t₂ • L.ω₂ = t₁ • L.basis 0 + t₂ • L.basis 1 from by simp]
  simp only [map_add, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.add_apply, Finsupp.single_apply]
  fin_cases i <;>
    simp [show (1 : Fin 2) ≠ 0 from by decide, show (0 : Fin 2) ≠ 1 from by decide]


/--
[mem_fundamentalParallelogram_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean)
-/
public theorem mem_fundamentalParallelogram_iff
  {L : ComplexLattice}
  {α z : ℂ} :
-- imply
  z ∈ fundamentalParallelogram L α ↔ ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ < 1 ∧ 0 ≤ t₂ ∧ t₂ < 1 ∧ z = α + t₁ • L.ω₁ + t₂ • L.ω₂ := by
-- proof
  simp only [fundamentalParallelogram, Set.mem_image, ZSpan.mem_fundamentalDomain]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨L.basis.repr w 0, L.basis.repr w 1, ?_⟩
    have h0 := hw 0; have h1 := hw 1
    simp only [Set.mem_Ico] at h0 h1
    refine ⟨h0.1, h0.2, h1.1, h1.2, ?_⟩
    have decomp : w = L.basis.repr w 0 • L.ω₁ + L.basis.repr w 1 • L.ω₂ := by
      have h := L.basis.sum_repr w
      rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at h
      exact h.symm
    conv_lhs => rw [decomp]
    ring
  · rintro ⟨t₁, t₂, ht₁0, ht₁1, ht₂0, ht₂1, rfl⟩
    refine ⟨t₁ • L.ω₁ + t₂ • L.ω₂, fun i => ?_, by ring⟩
    rw [basis_repr_omega (L := L)]
    fin_cases i <;> simp <;> constructor <;> linarith


/--
[mem_lattice_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lattice.lean)
-/
private theorem mem_lattice_iff_eq
  {L : ComplexLattice}
  {x : ℂ} :
-- imply
  x ∈ L.lattice ↔ ∃ n₁ n₂ : ℤ, (n₁ : ℂ) * L.ω₁ + (n₂ : ℂ) * L.ω₂ = x := by
-- proof
  apply ComplexLattice.mem_lattice_iff L


-- created on 2026-10-23
-- updated on 2026-11-23
