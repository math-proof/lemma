import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.LieGroups.code.GrothendieckGroupO.Part4
open ProjectiveFunctors Classical
open scoped TensorProduct


/--
[WeightBilinForm.form_posRoot_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/GrothendieckGroupO.lean)
-/
@[path]
lemma WeightBilinForm.form_posRoot_nonneg
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u}
  [CommRing R]
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {rd : PositiveRootData Δ}
  {alpha : Δ.𝔥 →ₗ[R] R}
-- given
  (halpha_pos : alpha ∈ rd.posRoots) :
-- imply
  (0 : R) ≤ B.form alpha alpha :=
-- proof
  B.pos_semidef alpha

private lemma WeightBilinForm.form_corootPairing_compat_ax
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {rd : PositiveRootData Δ}
  {alpha mu : Δ.𝔥 →ₗ[R] R}
-- given
  (halpha : alpha ∈ rd.posRoots) :
-- imply
  2 • B.form alpha mu = rd.corootPairing mu alpha * B.form alpha alpha :=
-- proof
  B.form_corootPairing_compat rd alpha mu halpha

private lemma dominant_corootPairing_diff_nonneg_ax
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u}
  [CommRing R]
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {lam phi alpha : Δ.𝔥 →ₗ[R] R}
-- given
  (hlam_dom : IsDominantWeightBruhat rd wg lam)
  (hphi_le : BruhatLE rd phi lam)
  (halpha_pos : alpha ∈ rd.posRoots) :
-- imply
  (0 : R) ≤ rd.corootPairing (lam - phi) alpha :=
-- proof
  B.dominant_corootPairing_diff_nonneg rd lam phi alpha hlam_dom hphi_le halpha_pos

private lemma WeightBilinForm.form_posRoot_dominant_diff_nonneg
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u}
  [CommRing R]
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {rd : PositiveRootData Δ}
  {lam phi alpha : Δ.𝔥 →ₗ[R] R}
-- given
  (hlam_dom : IsDominantWeightBruhat rd wg lam)
  (hphi_le : BruhatLE rd phi lam)
  (halpha_pos : alpha ∈ rd.posRoots) :
-- imply
  (0 : R) ≤ B.form alpha (lam - phi) := by
-- proof
  have hcompat := B.form_corootPairing_compat_ax rd alpha (lam - phi) halpha_pos
  have hpair_nonneg := dominant_corootPairing_diff_nonneg_ax rd wg B lam phi alpha hlam_dom hphi_le halpha_pos
  have haa_nonneg := B.pos_semidef alpha
  have hprod_nonneg : (0 : R) ≤ rd.corootPairing (lam - phi) alpha * B.form alpha alpha :=
    mul_nonneg hpair_nonneg haa_nonneg
  have h2_nonneg : (0 : R) ≤ 2 • B.form alpha (lam - phi) := by rw [hcompat]; exact hprod_nonneg
  rw [two_nsmul] at h2_nonneg
  linarith

private lemma WeightBilinForm.cross_terms_nonneg
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u}
  [CommRing R]
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {rd : PositiveRootData Δ}
  {lam phi alpha : Δ.𝔥 →ₗ[R] R}
  {n : ℕ}
-- given
  (hlam_dom : IsDominantWeightBruhat rd wg lam)
  (hphi_le : BruhatLE rd phi lam)
  (halpha_pos : alpha ∈ rd.posRoots)
  (_hn_pos : 0 < n) :
-- imply
  (0 : R) ≤ n • B.form alpha (lam - phi) + n • B.form alpha (lam - phi) + n • (n • B.form alpha alpha) := by
-- proof
  have h_cross := B.form_posRoot_dominant_diff_nonneg rd lam phi alpha hlam_dom hphi_le halpha_pos
  have h_sq := B.form_posRoot_nonneg rd alpha halpha_pos
  have h1 : (0 : R) ≤ n • B.form alpha (lam - phi) := nsmul_nonneg h_cross n
  have h2 : (0 : R) ≤ n • B.form alpha alpha := nsmul_nonneg h_sq n
  have h3 : (0 : R) ≤ n • (n • B.form alpha alpha) := nsmul_nonneg h2 n
  linarith

private lemma WeightBilinForm.form_coroot_compat_ax
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {rd : PositiveRootData Δ}
  {rs : RootSystemWithReflections rd wg}
  {alpha mu : Δ.𝔥 →ₗ[R] R}
-- given
  (halpha : alpha ∈ rs.allRoots) :
-- imply
  2 • B.form alpha mu = mu (rs.coroot alpha) * B.form alpha alpha :=
-- proof
  B.form_coroot_compat rd rs alpha mu halpha

private lemma WeightBilinForm.form_posRoot_pos_ax
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u}
  [CommRing R]
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {rd : PositiveRootData Δ}
  {alpha : Δ.𝔥 →ₗ[R] R}
-- given
  (halpha_pos : alpha ∈ rd.posRoots) :
-- imply
  (0 : R) < B.form alpha alpha :=
-- proof
  B.form_posRoot_pos rd alpha halpha_pos

private lemma WeightBilinForm.norm_diff_factor_ax
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {rd : PositiveRootData Δ}
  {rs : RootSystemWithReflections rd wg}
  {v alpha : Δ.𝔥 →ₗ[R] R}
  {n : ℕ}
-- given
  (halpha : alpha ∈ rs.allRoots) :
-- imply
  B.form (v + n • alpha) (v + n • alpha) - B.form v v = (n : R) * v (rs.coroot alpha) * B.form alpha alpha + (n : R) * (n : R) * B.form alpha alpha := by
-- proof
  have form_zero_left : ∀ (nu : Δ.𝔥 →ₗ[R] R), B.form 0 nu = 0 := by
    intro nu
    have h := B.bilin_left 0 0 nu
    rw [zero_add] at h
    have h2 : B.form 0 nu + 0 = B.form 0 nu + B.form 0 nu := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  have form_nsmul_left : ∀ (m : ℕ) (mu nu : Δ.𝔥 →ₗ[R] R),
    B.form (m • mu) nu = m • B.form mu nu := by
    intro m mu nu
    induction m with
    | zero => simp [form_zero_left nu]
    | succ m ih => rw [succ_nsmul, B.bilin_left, ih, succ_nsmul]
  have e1 : B.form v (v + n • alpha) = B.form v v + B.form v (n • alpha) := by
    rw [B.symm v (v + n • alpha), B.bilin_left, B.symm v v, B.symm (n • alpha) v]
  have e2 : B.form (n • alpha) (v + n • alpha) =
    B.form (n • alpha) v + B.form (n • alpha) (n • alpha) := by
    rw [B.symm (n • alpha) (v + n • alpha), B.bilin_left,
      B.symm v (n • alpha), B.symm (n • alpha) (n • alpha)]
  have hexpand : B.form (v + n • alpha) (v + n • alpha) =
    B.form v v + (n • B.form alpha v + n • B.form alpha v +
      n • (n • B.form alpha alpha)) := by
    rw [B.bilin_left, e1, e2]
    rw [form_nsmul_left n alpha v]
    rw [B.symm v (n • alpha), form_nsmul_left n alpha v]
    rw [form_nsmul_left n alpha (n • alpha), B.symm alpha (n • alpha),
      form_nsmul_left n alpha alpha]
    ring
  simp only [nsmul_eq_mul] at hexpand
  have hcompat := B.form_coroot_compat_ax rd rs alpha v halpha
  simp only [nsmul_eq_mul] at hcompat
  push_cast at hcompat
  have hdiff : B.form (v + n • alpha) (v + n • alpha) - B.form v v =
    ↑n * B.form alpha v + ↑n * B.form alpha v + ↑n * (↑n * B.form alpha alpha) := by
    have : B.form v v + (↑n * B.form alpha v + ↑n * B.form alpha v + ↑n * (↑n * B.form alpha alpha)) - B.form v v =
      ↑n * B.form alpha v + ↑n * B.form alpha v + ↑n * (↑n * B.form alpha alpha) := by ring
    rw [hexpand]; exact this
  have hcross : ↑n * B.form alpha v + ↑n * B.form alpha v = ↑n * (2 * B.form alpha v) := by ring
  rw [hdiff, hcross, hcompat]
  ring

private lemma WeightBilinForm.norm_eq_coroot_zero
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u}
  [CommRing R]
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {rd : PositiveRootData Δ}
  {rs : RootSystemWithReflections rd wg}
  {lam b alpha : Δ.𝔥 →ₗ[R] R}
  {n : ℕ}
-- given
  (hlam_dom : IsDominantWeightBruhat rd wg lam)
  (halpha_pos : alpha ∈ rd.posRoots)
  (hn_pos : 0 < n)
  (hpair : rd.corootPairing b alpha = (n : R))
  (h_eq : B.form (lam - b) (lam - b) = B.form (lam - b + n • alpha) (lam - b + n • alpha)) :
-- imply
  lam (rs.coroot alpha) = 0 := by
-- proof
  have hα_root : alpha ∈ rs.allRoots := rs.posRoots_sub alpha halpha_pos
  set v := lam - b with hv_def
  set aα := B.form alpha alpha with haα_def
  set c := lam (rs.coroot alpha) with hc_def
  have hdiff : B.form (v + n • alpha) (v + n • alpha) - B.form v v = 0 := by linarith
  have hfact := B.norm_diff_factor_ax rd rs v alpha n hα_root
  have hzero : (↑n : R) * v (rs.coroot alpha) * aα + (↑n : R) * (↑n : R) * aα = 0 := by
    linarith
  have hv_eval : v (rs.coroot alpha) = c - (↑n : R) := by
    simp only [hv_def, hc_def, LinearMap.sub_apply]
    rw [← rs.corootPairing_eq_eval alpha hα_root b]
    rw [hpair]
  rw [hv_eval] at hzero
  have hfactor : (↑n : R) * aα * c = 0 := by ring_nf; linarith
  have hn_pos_R : (0 : R) < (↑n : R) := Nat.cast_pos.mpr hn_pos
  have haα_pos : (0 : R) < aα := B.form_posRoot_pos_ax rd alpha halpha_pos
  have hna_pos : (0 : R) < (↑n : R) * aα := mul_pos hn_pos_R haα_pos
  have hna_ne : (↑n : R) * aα ≠ 0 := ne_of_gt hna_pos
  have hfactor' : (↑n : R) * aα * c = (↑n : R) * aα * 0 := by rw [mul_zero]; exact hfactor
  exact mul_left_cancel₀ hna_ne hfactor'

private lemma WeightBilinForm.dominant_posRoot_cross_le
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {R : Type u}
  [CommRing R]
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {rd : PositiveRootData Δ}
  {lam phi alpha : Δ.𝔥 →ₗ[R] R}
  {n : ℕ}
-- given
  (hlam_dom : IsDominantWeightBruhat rd wg lam)
  (hphi_le : BruhatLE rd phi lam)
  (halpha_pos : alpha ∈ rd.posRoots)
  (hn_pos : 0 < n) :
-- imply
  B.form (lam - phi) (lam - phi) ≤ B.form (lam - phi) (lam - phi) + (n • B.form alpha (lam - phi) + n • B.form alpha (lam - phi) + n • (n • B.form alpha alpha)) :=
-- proof
  le_add_of_nonneg_right (B.cross_terms_nonneg rd lam phi alpha n hlam_dom hphi_le halpha_pos hn_pos)

private lemma hom_multiplicity_eq_pairing
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {KO : GrothendieckGroupData Δ}
  {ip : KO.InnerProductData}
  {fF : InducedMapData KO}
  {lam mu : Δ.𝔥 →ₗ[R] R} :
-- imply
  ip.pairing (fF.mapKO (KO.delta lam)) (KO.delta mu) = homDim KO ip fF lam mu :=
-- proof
  rfl

private lemma adjunction_preserves_homDim
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {KO : GrothendieckGroupData Δ}
  {ip : KO.InnerProductData}
  {fF fFv : InducedMapData KO}
  {lam mu : Δ.𝔥 →ₗ[R] R}
-- given
  (adj : AdjointPairData (R := R) (𝔤 := 𝔤))
  (hfF : fF.F = adj.F)
  (hfFv : fFv.F = adj.Fv) :
-- imply
  homDim KO ip fF lam mu = homDim KO ip fFv mu lam :=
-- proof
  adj.adjunction_homDim_pairing KO ip fF fFv hfF hfFv lam mu

private lemma adjoint_pair_basis_pairing
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {KO : GrothendieckGroupData Δ}
  {ip : KO.InnerProductData}
  {fF fFv : InducedMapData KO}
-- given
  (adj : AdjointPairData (R := R) (𝔤 := 𝔤))
  (hfF : fF.F = adj.F)
  (hfFv : fFv.F = adj.Fv) :
-- imply
  ∀ (lam mu : Δ.𝔥 →ₗ[R] R), ip.pairing (fF.mapKO (KO.delta lam)) (KO.delta mu) = ip.pairing (KO.delta lam) (fFv.mapKO (KO.delta mu)) := by
-- proof
  intro lam mu
  have pairing_symm : ∀ a b, ip.pairing a b = ip.pairing b a :=
    ip.pairing_basis_determines _ _ (fun l m => by
      rw [ip.orthonormal, ip.orthonormal]; simp [eq_comm])
  have hadj := adj.adjunction_homDim_pairing KO ip fF fFv hfF hfFv lam mu
  rwa [pairing_symm (KO.delta lam) (fFv.mapKO (KO.delta mu))]

private lemma theorem_23_1_ii
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {KO : GrothendieckGroupData Δ}
  {ip : KO.InnerProductData}
  {fF fFv : InducedMapData KO}
-- given
  (adj : AdjointPairData (R := R) (𝔤 := 𝔤))
  (hfF : fF.F = adj.F)
  (hfFv : fFv.F = adj.Fv) :
-- imply
  ∀ (x y : KO.carrier), ip.pairing (fF.mapKO x) y = ip.pairing x (fFv.mapKO y) := by
-- proof
  have hbasis := adjoint_pair_basis_pairing KO ip adj fF fFv hfF hfFv
  exact ip.pairing_basis_determines
    (fun x y => ip.pairing (fF.mapKO x) y)
    (fun x y => ip.pairing x (fFv.mapKO y))
    hbasis

private lemma inner_product_nondegen
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {Δ : TriangularDecomposition R 𝔤}
  {KO : GrothendieckGroupData Δ}
  {ip : KO.InnerProductData}
  {a b : KO.carrier}
-- given
  (h : ∀ mu : Δ.𝔥 →ₗ[R] R, ip.pairing (KO.delta mu) a = ip.pairing (KO.delta mu) b) :
-- imply
  a = b := by
-- proof
  have delta_surj : ∀ (c : KO.carrier), ∃ lam, KO.delta lam = c := by
    intro c
    by_contra hc
    push Not at hc
    have key := ip.pairing_basis_determines
      (fun x _ => if x = c then (1 : ℤ) else 0)
      (fun _ _ => (0 : ℤ))
      (fun lam _ => by simp [if_neg (hc lam)])
    have := key c c
    simp at this
  obtain ⟨la, hla⟩ := delta_surj a
  obtain ⟨lb, hlb⟩ := delta_surj b
  have h_la := h la
  rw [← hla, ← hlb] at h_la
  rw [ip.orthonormal la la, ip.orthonormal la lb] at h_la
  simp at h_la
  rw [← hla, ← hlb, h_la]

private lemma direct_summand_preserves_exact
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {F G : EndoFunctorData R 𝔤}
  {M₁ M₂ M₃ : RepGfObj R 𝔤}
  {f : RepGfHom M₁ M₂}
  {g : RepGfHom M₂ M₃}
-- given
  (h_summand : IsDirectSummand F G)
  (hG_exact : ∀ {M₁ M₂ M₃ : RepGfObj R 𝔤} (f : RepGfHom M₁ M₂) (g : RepGfHom M₂ M₃) (_hex : IsExactSequence f g), IsExactSequence (G.mapHom f) (G.mapHom g))
  (hex : IsExactSequence f g) :
-- imply
  IsExactSequence (F.mapHom f) (F.mapHom g) := by
-- proof
  obtain ⟨i, p, hpi⟩ := h_summand
  have hG := hG_exact f g hex
  intro m
  constructor
  ·
    intro hm
    have hi_nat_g := i.naturality g m
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hi_nat_g
    have hi_zero : (i.app M₃).toFun ((F.mapHom g).toFun m) = 0 := by
      rw [hm, map_zero]
    rw [hi_nat_g] at hi_zero
    have ⟨y, hy⟩ := (hG ((i.app M₂).toFun m)).mp hi_zero
    use (p.app M₁).toFun y
    have hp_nat_f := p.naturality f y
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hp_nat_f
    rw [← hp_nat_f, hy]
    have hpi_M₂ := hpi M₂ m
    simp only [NatTransData.comp, RepGfHom.comp, LieModuleHom.coe_comp,
      Function.comp_apply, NatTransData.id, RepGfHom.id,
      LieModuleHom.coe_id, id_eq] at hpi_M₂
    exact hpi_M₂
  ·
    rintro ⟨x, hx⟩
    rw [← hx]
    have hi_nat_f := i.naturality f x
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hi_nat_f
    have hi_nat_g := i.naturality g ((F.mapHom f).toFun x)
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hi_nat_g
    rw [hi_nat_f] at hi_nat_g
    have hker : (G.mapHom g).toFun ((G.mapHom f).toFun ((i.app M₁).toFun x)) = 0 := by
      exact (hG ((G.mapHom f).toFun ((i.app M₁).toFun x))).mpr ⟨(i.app M₁).toFun x, rfl⟩
    rw [hker] at hi_nat_g
    have hpi_M₃ := hpi M₃ ((F.mapHom g).toFun ((F.mapHom f).toFun x))
    simp only [NatTransData.comp, RepGfHom.comp, LieModuleHom.coe_comp,
      Function.comp_apply, NatTransData.id, RepGfHom.id,
      LieModuleHom.coe_id, id_eq] at hpi_M₃
    rw [← hpi_M₃, hi_nat_g, map_zero]

private lemma InnerProductData.pairing_symm
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {KO : GrothendieckGroupData Δ}
  {ip : KO.InnerProductData}
  {x y : KO.carrier} :
-- imply
  ip.pairing x y = ip.pairing y x := by
-- proof
  apply ip.pairing_basis_determines (fun a b => ip.pairing a b) (fun a b => ip.pairing b a)
  intro lam mu
  rw [ip.orthonormal, ip.orthonormal]
  simp [eq_comm]

private lemma dominatesSet_implies_isDominantWeightLE
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {lam : Δ.𝔥 →ₗ[R] R}
  {S : Set (Δ.𝔥 →ₗ[R] R)}
-- given
  (hdom : DominatesSet rd lam S)
  (h_orbit : ∀ w ∈ WeylStabilizerModQ rd wg lam, wg.dualAction w lam ∈ S) :
-- imply
  IsDominantWeightLE rd wg lam := by
-- proof
  intro w hw hle
  have h_wle : WeightLE rd (wg.dualAction w lam) lam := hdom (wg.dualAction w lam) (h_orbit w hw)
  exact weightLE_antisymm rd _ _ hle h_wle

private lemma summand_of_translation_factors_through_block
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {lam : Δ.𝔥 →ₗ[R] R}
  {G_L : EndoFunctorData R 𝔤}
  {F_j : EndoFunctorData R 𝔤}
  {ι : Type u}
  [Fintype ι]
  {F_i : ι → EndoFunctorData R 𝔤}
  {j : ι}
-- given
  (_hG : IsProjectiveFunctor G_L)
  (hG_block : FactorsThroughBlock Δ G_L lam)
  (_hF : IsProjectiveFunctor F_j)
  (_hIndec : IsIndecomposable F_j)
  (hDecomp : IsDirectSumDecompGen G_L F_i)
  (hj : F_j = F_i j) :
-- imply
  FactorsThroughBlock Δ F_j lam := by
-- proof
  obtain ⟨section_i, retract_i, hRetSec, _hSum⟩ := hDecomp
  intro M hM x
  have hRS := hRetSec j
  subst hj
  have hRS_M := hRS M
  have hRS_x := hRS_M x
  simp only [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id,
    LieModuleHom.coe_comp, Function.comp_apply, LieModuleHom.id_apply] at hRS_x
  have h_sec_zero : (section_i j |>.app M).toFun x = 0 := by
    exact hG_block M hM ((section_i j |>.app M).toFun x)
  rw [h_sec_zero] at hRS_x
  rw [← hRS_x]
  exact map_zero (retract_i j |>.app M).toFun

private lemma IsInQPlus_antisymm
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {μ : Δ.𝔥 →ₗ[R] R}
-- given
  (hpos : rd.IsInQPlus μ)
  (hneg : rd.IsInQPlus (-μ)) :
-- imply
  μ = 0 := by
-- proof
  obtain ⟨c, hc⟩ := hpos
  obtain ⟨d, hd⟩ := hneg
  by_contra hμ
  have hne : ∃ β ∈ rd.posRoots, c β ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hμ
    rw [hc]
    apply Finset.sum_eq_zero
    intro β hβ
    simp [hall β hβ]
  obtain ⟨β, hβ, hcβ⟩ := hne
  have hsum : ∑ α ∈ rd.posRoots, ((c α + d α) • α) = 0 := by
    have h0 : ∑ α ∈ rd.posRoots, (c α) • α + ∑ α ∈ rd.posRoots, (d α) • α = 0 := by
      rw [← hc, ← hd, add_neg_cancel]
    rw [← Finset.sum_add_distrib] at h0
    convert h0 using 1
    apply Finset.sum_congr rfl
    intro α _
    rw [add_nsmul]
  have hextract := Finset.sum_erase_add _ (fun α => (c α + d α) • α) hβ
  rw [hsum] at hextract
  let c' : (Δ.𝔥 →ₗ[R] R) → ℕ := fun γ => if γ = β then 0 else c γ + d γ
  have hc'_sum : ∑ γ ∈ rd.posRoots, (c' γ) • γ =
    ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ := by
    rw [← Finset.sum_erase_add _ _ hβ]
    simp only [c', ite_true, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro γ hγ
    have hne : γ ≠ β := Finset.ne_of_mem_erase hγ
    simp [hne]
  have hkey : (-(↑(c β + d β) : ℤ)) • β = ∑ γ ∈ rd.posRoots, (c' γ) • γ := by
    rw [hc'_sum]
    have h1 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ + (c β + d β) • β = 0 := hextract
    have h2 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ = -((c β + d β) • β) :=
      eq_neg_of_add_eq_zero_left h1
    rw [h2, neg_zsmul, natCast_zsmul]
  have hn_neg : (-(↑(c β + d β) : ℤ)) < 0 := by
    have : 0 < c β := Nat.pos_of_ne_zero hcβ
    omega
  exact rd.posRoots_pointed_cone β hβ _ hn_neg ⟨c', hkey⟩

private lemma WeightBilinForm.form_zero_left
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {nu : Δ.𝔥 →ₗ[R] R} :
-- imply
  B.form 0 nu = 0 := by
-- proof
  have h := B.bilin_left 0 0 nu
  rw [zero_add] at h
  have : B.form 0 nu + B.form 0 nu - B.form 0 nu = B.form 0 nu - B.form 0 nu := by
    rw [← h]
  simp [add_sub_cancel_right] at this
  exact this

private lemma WeightBilinForm.form_nsmul_left
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {n : ℕ}
  {mu nu : Δ.𝔥 →ₗ[R] R} :
-- imply
  B.form (n • mu) nu = n • B.form mu nu := by
-- proof
  induction n with
  | zero => simp [B.form_zero_left nu]
  | succ n ih =>
    rw [succ_nsmul, B.bilin_left, ih, succ_nsmul]

private lemma WeightBilinForm.form_expand
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {v alpha : Δ.𝔥 →ₗ[R] R}
  {n : ℕ} :
-- imply
  B.form (v + n • alpha) (v + n • alpha) = B.form v v + (n • B.form alpha v + n • B.form alpha v + n • (n • B.form alpha alpha)) := by
-- proof
  rw [B.bilin_left]
  have e1 : B.form v (v + n • alpha) = B.form v v + B.form v (n • alpha) := by
    rw [B.symm v (v + n • alpha), B.bilin_left, B.symm v v, B.symm (n • alpha) v]
  have e2 : B.form (n • alpha) (v + n • alpha) =
    B.form (n • alpha) v + B.form (n • alpha) (n • alpha) := by
    rw [B.symm (n • alpha) (v + n • alpha), B.bilin_left,
      B.symm v (n • alpha), B.symm (n • alpha) (n • alpha)]
  rw [e1, e2]
  rw [B.form_nsmul_left n alpha v]
  rw [B.symm v (n • alpha), B.form_nsmul_left n alpha v]
  rw [B.form_nsmul_left n alpha (n • alpha), B.symm alpha (n • alpha),
    B.form_nsmul_left n alpha alpha]
  ring

private lemma norm_sq_dominant_reflection_nonneg_diff
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {R : Type u}
  [CommRing R]
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {lam phi alpha : Δ.𝔥 →ₗ[R] R}
  {n : ℕ}
-- given
  (hlam_dom : IsDominantWeightBruhat rd wg lam)
  (hphi_le : BruhatLE rd phi lam)
  (halpha_pos : alpha ∈ rd.posRoots)
  (hn_pos : 0 < n) :
-- imply
  B.normSq (lam - phi) ≤ B.normSq (lam - phi + n • alpha) := by
-- proof
  unfold WeightBilinForm.normSq
  have hexpand := B.form_expand (lam - phi) alpha n
  have hle := B.dominant_posRoot_cross_le rd lam phi alpha n hlam_dom hphi_le halpha_pos hn_pos
  rwa [hexpand]

private lemma norm_sq_single_step_le
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {R : Type u}
  [CommRing R]
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {lam a b : Δ.𝔥 →ₗ[R] R}
-- given
  (hlam_dom : IsDominantWeightBruhat rd wg lam)
  (hb_le : BruhatLE rd b lam)
  (hstep : ∃ α, ReflectionLT rd α a b) :
-- imply
  B.normSq (lam - b) ≤ B.normSq (lam - a) := by
-- proof
  obtain ⟨α, hα_pos, n, hn_pos, _hpair, hab⟩ := hstep
  have hkey : lam - a = lam - b + n • α := by
    rw [hab]; abel
  rw [hkey]
  exact norm_sq_dominant_reflection_nonneg_diff rd wg B lam b α n hlam_dom hb_le hα_pos hn_pos

private lemma corootPairing_eq_coroot_eval_ax
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {rs : RootSystemWithReflections rd wg}
  {μ α : Δ.𝔥 →ₗ[R] R}
-- given
  (hα : α ∈ rs.allRoots) :
-- imply
  rd.corootPairing μ α = μ (rs.coroot α) :=
-- proof
  rs.corootPairing_eq_eval α hα μ

private lemma norm_sq_equality_implies_lam_coroot_zero_ax
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {R : Type u}
  [CommRing R]
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {rs : RootSystemWithReflections rd wg}
  {B : WeightBilinForm wg}
  {lam b α : Δ.𝔥 →ₗ[R] R}
  {n : ℕ}
-- given
  (hlam_dom : IsDominantWeightBruhat rd wg lam)
  (hα_pos : α ∈ rd.posRoots)
  (hn_pos : 0 < n)
  (hpair : rd.corootPairing b α = (n : R))
  (h_eq : B.normSq (lam - b) = B.normSq (lam - b + n • α)) :
-- imply
  lam (rs.coroot α) = 0 :=
-- proof
  B.norm_eq_coroot_zero rd rs lam b α n hlam_dom hα_pos hn_pos hpair h_eq

private lemma norm_sq_reflection_equality_weyl_element
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {R : Type u}
  [CommRing R]
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {rs : RootSystemWithReflections rd wg}
  {B : WeightBilinForm wg}
  {lam b α : Δ.𝔥 →ₗ[R] R}
  {n : ℕ}
-- given
  (hlam_dom : IsDominantWeightBruhat rd wg lam)
  (hα_pos : α ∈ rd.posRoots)
  (hn_pos : 0 < n)
  (hpair : rd.corootPairing b α = (n : R))
  (h_eq : B.normSq (lam - b) = B.normSq (lam - b + n • α)) :
-- imply
  ∃ (w : wg.W), w ∈ WeylStabilizer rd wg lam ∧ wg.dualAction w b = b - n • α := by
-- proof
  have hα_root : α ∈ rs.allRoots := rs.posRoots_sub α hα_pos
  have hlam_zero : lam (rs.coroot α) = 0 :=
    norm_sq_equality_implies_lam_coroot_zero_ax rd wg rs B lam b α n
      hlam_dom hα_pos hn_pos hpair h_eq
  have hrefl_lam : wg.dualAction (rs.reflection α) lam = lam := by
    rw [rs.reflection_formula α hα_root lam, hlam_zero, zero_smul, sub_zero]
  have hcompat : b (rs.coroot α) = (n : R) := by
    rwa [← corootPairing_eq_coroot_eval_ax rd wg rs b α hα_root]
  have hrefl_b : wg.dualAction (rs.reflection α) b = b - n • α := by
    rw [rs.reflection_formula α hα_root b, hcompat]
    congr 1
    exact Nat.cast_smul_eq_nsmul R n α
  have hs_stab : rs.reflection α ∈ WeylStabilizer rd wg lam := hrefl_lam
  exact ⟨rs.reflection α, hs_stab, hrefl_b⟩

private lemma norm_sq_single_step_eq
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {R : Type u}
  [CommRing R]
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {rs : RootSystemWithReflections rd wg}
  {B : WeightBilinForm wg}
  {lam a b : Δ.𝔥 →ₗ[R] R}
-- given
  (hlam_dom : IsDominantWeightBruhat rd wg lam)
  (hstep : ∃ α, ReflectionLT rd α a b)
  (h_eq : B.normSq (lam - b) = B.normSq (lam - a)) :
-- imply
  ∃ (w : wg.W), w ∈ WeylStabilizer rd wg lam ∧ wg.dualAction w b = a := by
-- proof
  obtain ⟨α, hα_pos, n, hn_pos, hpair, hab⟩ := hstep
  have hkey : lam - a = lam - b + n • α := by
    rw [hab]; abel
  rw [hkey] at h_eq
  obtain ⟨w, hw_stab, hw_act⟩ :=
    norm_sq_reflection_equality_weyl_element rd wg rs B lam b α n hlam_dom hα_pos hn_pos hpair h_eq
  exact ⟨w, hw_stab, hw_act.trans hab.symm⟩

private lemma lemma_23_4_i
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {B : WeightBilinForm wg}
  {lam phi psi : Δ.𝔥 →ₗ[R] R}
-- given
  (hlam_dom : IsDominantWeightBruhat rd wg lam)
  (hBruhat : BruhatLE rd psi phi)
  (hphi_le_lam : BruhatLE rd phi lam) :
-- imply
  B.normSq (lam - phi) ≤ B.normSq (lam - psi) := by
-- proof
  induction hBruhat with
  | refl => exact le_rfl
  | @tail b c _hab hbc ih =>
    have hb_le_c : BruhatLE rd b c := Relation.ReflTransGen.single hbc
    have hb_le_lam : BruhatLE rd b lam := hb_le_c.trans hphi_le_lam
    exact le_trans (norm_sq_single_step_le rd wg B lam b c hlam_dom hphi_le_lam hbc)
      (ih hb_le_lam)

private lemma lemma_23_4_ii
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {rs : RootSystemWithReflections rd wg}
  {B : WeightBilinForm wg}
  {lam phi psi : Δ.𝔥 →ₗ[R] R}
-- given
  (hlam_dom : IsDominantWeightBruhat rd wg lam)
  (hBruhat : BruhatLE rd psi phi)
  (hphi_le_lam : BruhatLE rd phi lam)
  (h_eq : B.normSq (lam - phi) = B.normSq (lam - psi)) :
-- imply
  ∃ (w : wg.W), w ∈ WeylStabilizer rd wg lam ∧ wg.dualAction w phi = psi := by
-- proof
  induction hBruhat with
  | refl =>
    exact ⟨1, wg.dualAction_one lam, wg.dualAction_one psi⟩
  | @tail b c hab hbc ih =>
    have hb_le_c : BruhatLE rd b c := Relation.ReflTransGen.single hbc
    have hb_le_lam : BruhatLE rd b lam := hb_le_c.trans hphi_le_lam
    have hstep_le := norm_sq_single_step_le rd wg B lam b c hlam_dom hphi_le_lam hbc
    have hchain_le := lemma_23_4_i rd wg B lam b psi hlam_dom hab hb_le_lam
    have h_eq_step : B.normSq (lam - c) = B.normSq (lam - b) :=
      le_antisymm hstep_le (h_eq ▸ hchain_le)
    have h_eq_chain : B.normSq (lam - b) = B.normSq (lam - psi) :=
      le_antisymm hchain_le (h_eq_step ▸ h_eq ▸ le_rfl)
    obtain ⟨w₁, hw₁_stab, hw₁_act⟩ := norm_sq_single_step_eq rd wg rs B lam b c hlam_dom hbc h_eq_step
    obtain ⟨w₂, hw₂_stab, hw₂_act⟩ := ih hb_le_lam h_eq_chain
    exact ⟨w₂ * w₁,
      WeylStabilizer_mul_closed rd wg lam hw₂_stab hw₁_stab,
      by rw [wg.dualAction_mul, hw₁_act, hw₂_act]⟩

private lemma bilinForm_weyl_normSq_invariant
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {w : wg.W}
  {mu nu : Δ.𝔥 →ₗ[R] R} :
-- imply
  B.normSq (wg.dualAction w mu - wg.dualAction w nu) = B.normSq (mu - nu) :=
-- proof
B.weyl_normSq_invariant w mu nu

private lemma normSq_weyl_invariant
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {B : WeightBilinForm wg}
  {a b : Δ.𝔥 →ₗ[R] R}
  {w : wg.W} :
-- imply
  B.normSq (wg.dualAction w a - wg.dualAction w b) = B.normSq (a - b) :=
-- proof
bilinForm_weyl_normSq_invariant wg B w a b

private lemma weylStabilizer_fixes_dominant_lam
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {lam : Δ.𝔥 →ₗ[R] R}
  {w : wg.W}
-- given
  (_hlam_dom : IsDominantWeightBruhat rd wg lam)
  (hw_stab : w ∈ WeylStabilizer rd wg lam) :
-- imply
  wg.dualAction w lam = lam :=
-- proof
  hw_stab

private lemma natiso_from_verma_iso
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {F₁ F₂ : EndoFunctorData R 𝔤}
  {lam : Δ.𝔥 →ₗ[R] R}
  {Mverma_lam : RepGfObj R 𝔤}
  {iso_fwd : RepGfHom (F₁.obj Mverma_lam) (F₂.obj Mverma_lam)}
  {iso_bwd : RepGfHom (F₂.obj Mverma_lam) (F₁.obj Mverma_lam)}
-- given
  (_hF₁ : IsProjectiveFunctor F₁)
  (_hF₂ : IsProjectiveFunctor F₂)
  (_hI₁ : IsIndecomposable F₁)
  (_hI₂ : IsIndecomposable F₂)
  (_hVerma_lam : IsVermaModule Δ Mverma_lam.carrier (lam - wg.ρ))
  (_hiso₁ : (iso_bwd.comp iso_fwd).EqAsMap (RepGfHom.id _))
  (_hiso₂ : (iso_fwd.comp iso_bwd).EqAsMap (RepGfHom.id _)) :
-- imply
  AreNatIso F₁ F₂ := by
-- proof
  exact corollary_22_6_i_areNatIso Δ wg lam F₁ F₂ _hF₁ _hF₂ Mverma_lam
    ⟨_hVerma_lam⟩ iso_fwd iso_bwd _hiso₁ _hiso₂

private lemma multiplicity_free_wall_crossing
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {C : CoxeterGroupData}
  {KOB : GrothendieckGroupBlock Δ wg}
  {s : C.W}
  {fF_mapKO : KOB.carrier → KOB.carrier}
  {compat : CoxeterWeylCompatibility C rd wg}
  {wact : wg.W → KOB.carrier → KOB.carrier}
-- given
  (_hs : s ∈ C.simpleReflections)
  (fF_equivariant : ∀ (w_act : wg.W) (x : KOB.carrier), wact w_act (fF_mapKO x) = fF_mapKO (wact w_act x))
  (wact_basis : ∀ (w_act v : wg.W), wact w_act (KOB.delta_w v) = KOB.delta_w (w_act * v))
  (wact_add : ∀ (w_act : wg.W) (x y : KOB.carrier), letI := KOB.instACG wact w_act (x + y) = wact w_act x + wact w_act y)
  (fF_base : letI := KOB.instACG; fF_mapKO (KOB.delta_w 1) = KOB.delta_w 1 + KOB.delta_w (compat.ι s)) :
-- imply
  ∀ (w : C.W), letI := KOB.instACG fF_mapKO (KOB.delta_w (compat.ι w)) = KOB.delta_w (compat.ι w) + KOB.delta_w (compat.ι w * compat.ι s) := by
-- proof
  intro w
  have h1 := fF_equivariant (compat.ι w) (KOB.delta_w 1)
  rw [wact_basis (compat.ι w) 1, mul_one] at h1
  rw [← h1]
  rw [fF_base]
  rw [wact_add]
  rw [wact_basis, wact_basis]
  rw [mul_one]

private lemma toWeak_F_eq
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
-- given
  (adj : AdjointPairData (R := R) (𝔤 := 𝔤)) :
-- imply
  adj.toWeak.F = adj.F := by
-- proof
  apply AdjointPairData.toWeak_F adj

private lemma toWeak_Fv_eq
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
-- given
  (adj : AdjointPairData (R := R) (𝔤 := 𝔤)) :
-- imply
  adj.toWeak.Fv = adj.Fv := by
-- proof
  apply AdjointPairData.toWeak_Fv adj


-- created on 2026-10-24
