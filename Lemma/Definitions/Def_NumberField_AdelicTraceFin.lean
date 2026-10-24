import Lemma.Definitions.Def_NumberField_AdelicTraceProducer
import Lemma.Definitions.Def_NumberField_IntegralAdelicTrace
import Lemma.Definitions.Def_NumberField_AdelicBox
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

set_option synthInstance.maxHeartbeats 100000

namespace NumberField.StandardAddChar

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicTrace Topology Filter

section FiniteTrace

variable (K : Type) [Field K] [NumberField K]

private def sm (z : Π v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) : FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite z

private theorem sm_apply (z : Π v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
    (v : HeightOneSpectrum (𝓞 K)) : sm K z v = (z v : v.adicCompletion K) := rfl

private theorem sm_add (x y : Π v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) :
    sm K (x + y) = sm K x + sm K y :=
  RestrictedProduct.ext _ _ fun v => rfl

private theorem sm_zero : sm K 0 = 0 := RestrictedProduct.ext _ _ fun v => rfl

private def smHom : (Π v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) →+ FiniteAdeleRing (𝓞 K) K where
  toFun := sm K
  map_zero' := sm_zero K
  map_add' := sm_add K

private theorem continuous_sm : Continuous (sm K) :=
  (RestrictedProduct.isEmbedding_structureMap).continuous

private theorem sm_mem (z : Π v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) :
    sm K z ∈ integralFiniteAdeles (𝓞 K) K := fun v => (z v).2

private theorem sm_diag (a : 𝓞 K) :
    sm K (diag K a) = algebraMap K (FiniteAdeleRing (𝓞 K) K) (a : K) :=
  RestrictedProduct.ext _ _ fun v => by
    change ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) a : v.adicCompletion K)) = _
    rw [coe_algebraMap_adicCompletionIntegers]
    rfl

private def pre (z : FiniteAdeleRing (𝓞 K) K) (hz : z ∈ integralFiniteAdeles (𝓞 K) K) :
    Π v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K := fun v => ⟨z v, hz v⟩

private theorem sm_pre (z : FiniteAdeleRing (𝓞 K) K) (hz : z ∈ integralFiniteAdeles (𝓞 K) K) :
    sm K (pre K z hz) = z := RestrictedProduct.ext _ _ fun v => rfl

private theorem pre_sm (w : Π v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) :
    pre K (sm K w) (sm_mem K w) = w := funext fun v => Subtype.ext rfl

private theorem pre_add (z₁ z₂ : FiniteAdeleRing (𝓞 K) K) (h₁ : z₁ ∈ integralFiniteAdeles (𝓞 K) K)
    (h₂ : z₂ ∈ integralFiniteAdeles (𝓞 K) K) (h : z₁ + z₂ ∈ integralFiniteAdeles (𝓞 K) K) :
    pre K (z₁ + z₂) h = pre K z₁ h₁ + pre K z₂ h₂ := funext fun v => Subtype.ext rfl

private theorem exists_eq_of_algebraMap_mem {ξ : K}
    (h : algebraMap K (FiniteAdeleRing (𝓞 K) K) ξ ∈ integralFiniteAdeles (𝓞 K) K) :
    ∃ a : 𝓞 K, (a : K) = ξ := by
  have hint : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K ξ ≤ 1 := fun v => by
    have hv : (algebraMap K (FiniteAdeleRing (𝓞 K) K) ξ) v ∈ v.adicCompletionIntegers K := h v
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap K (FiniteAdeleRing (𝓞 K) K) ξ) v = (ξ : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ξ hint
  exact ⟨a, by rw [RingOfIntegers.coe_eq_algebraMap]; exact ha⟩

variable (F : Type) [Field F] [NumberField F]

private def traceFinAux (x : FiniteAdeleRing (𝓞 F) F) (k : F)
    (hk : algebraMap F (FiniteAdeleRing (𝓞 F) F) k + x ∈ integralFiniteAdeles (𝓞 F) F) :
    FiniteAdeleRing (𝓞 ℚ) ℚ :=
  sm ℚ (traceInt F (pre F _ hk)) - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (Algebra.trace ℚ F k)

private theorem sm_traceInt_diag (a : 𝓞 F) :
    sm ℚ (traceInt F (diag F a)) = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (Algebra.trace ℚ F (a : F)) := by
  rw [traceInt_diag, ← diag_eq, sm_diag, ← Algebra.coe_trace_int]
  congr 1

private theorem traceFinAux_eq (x : FiniteAdeleRing (𝓞 F) F) (k k' : F)
    (hk : algebraMap F (FiniteAdeleRing (𝓞 F) F) k + x ∈ integralFiniteAdeles (𝓞 F) F)
    (hk' : algebraMap F (FiniteAdeleRing (𝓞 F) F) k' + x ∈ integralFiniteAdeles (𝓞 F) F) :
    traceFinAux F x k hk = traceFinAux F x k' hk' := by

  have hdiff : algebraMap F (FiniteAdeleRing (𝓞 F) F) (k - k') ∈ integralFiniteAdeles (𝓞 F) F := by
    have : algebraMap F (FiniteAdeleRing (𝓞 F) F) (k - k')
        = (algebraMap F _ k + x) - (algebraMap F _ k' + x) := by rw [(algebraMap F (FiniteAdeleRing (𝓞 F) F)).map_sub]; ring
    rw [this]
    exact fun v => sub_mem (hk v) (hk' v)
  obtain ⟨a, ha⟩ := exists_eq_of_algebraMap_mem F hdiff

  have hpre : pre F _ hk = pre F _ hk' + diag F a := by
    funext v
    apply Subtype.ext
    show (algebraMap F (FiniteAdeleRing (𝓞 F) F) k + x) v
        = (algebraMap F (FiniteAdeleRing (𝓞 F) F) k' + x) v + (diag F a v : v.adicCompletion F)
    rw [diag_apply, coe_algebraMap_adicCompletionIntegers]
    have hk_eq : k = k' + (a : F) := by rw [ha]; ring
    rw [hk_eq, (algebraMap F (FiniteAdeleRing (𝓞 F) F)).map_add]
    show ((algebraMap F _ k' + algebraMap F _ (a : F)) + x) v = _
    rw [add_right_comm]
    rfl
  unfold traceFinAux
  rw [hpre, (traceInt F).map_add, sm_add, sm_traceInt_diag, ha, (Algebra.trace ℚ F).map_sub,
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).map_sub]
  ring

def traceFinHom : FiniteAdeleRing (𝓞 F) F →+ FiniteAdeleRing (𝓞 ℚ) ℚ :=
  AddMonoidHom.mk' (fun x => traceFinAux F x (Classical.choose (exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F x))
      (Classical.choose_spec (exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F x))) (by
    intro x y
    set kx := Classical.choose (exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F x)
    have hkx := Classical.choose_spec (exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F x)
    set ky := Classical.choose (exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F y)
    have hky := Classical.choose_spec (exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F y)
    have hkxy : algebraMap F (FiniteAdeleRing (𝓞 F) F) (kx + ky) + (x + y) ∈ integralFiniteAdeles (𝓞 F) F := by
      have : algebraMap F (FiniteAdeleRing (𝓞 F) F) (kx + ky) + (x + y)
          = (algebraMap F _ kx + x) + (algebraMap F _ ky + y) := by rw [(algebraMap F (FiniteAdeleRing (𝓞 F) F)).map_add]; ring
      rw [this]; exact fun v => add_mem (hkx v) (hky v)
    show traceFinAux F (x + y) _ _ = traceFinAux F x kx hkx + traceFinAux F y ky hky
    rw [traceFinAux_eq F (x + y) _ (kx + ky) _ hkxy]
    unfold traceFinAux
    have hpre : pre F _ hkxy = pre F _ hkx + pre F _ hky := by
      funext v; apply Subtype.ext
      show (algebraMap F (FiniteAdeleRing (𝓞 F) F) (kx + ky) + (x + y)) v = _
      rw [show algebraMap F (FiniteAdeleRing (𝓞 F) F) (kx + ky) + (x + y)
          = (algebraMap F _ kx + x) + (algebraMap F _ ky + y) by rw [(algebraMap F (FiniteAdeleRing (𝓞 F) F)).map_add]; ring]
      rfl
    rw [hpre, (traceInt F).map_add, sm_add, (Algebra.trace ℚ F).map_add,
      (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).map_add]
    ring)

private theorem traceFinHom_eq (x : FiniteAdeleRing (𝓞 F) F) (k : F)
    (hk : algebraMap F (FiniteAdeleRing (𝓞 F) F) k + x ∈ integralFiniteAdeles (𝓞 F) F) :
    traceFinHom F x = sm ℚ (traceInt F (pre F _ hk)) - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (Algebra.trace ℚ F k) :=
  traceFinAux_eq F x _ k _ hk

theorem traceFinHom_algebraMap (q : F) :
    traceFinHom F (algebraMap F (FiniteAdeleRing (𝓞 F) F) q)
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (Algebra.trace ℚ F q) := by
  have h0 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (-q) + algebraMap F (FiniteAdeleRing (𝓞 F) F) q
      ∈ integralFiniteAdeles (𝓞 F) F := by
    rw [(algebraMap F (FiniteAdeleRing (𝓞 F) F)).map_neg, neg_add_cancel]; exact fun v => zero_mem _
  rw [traceFinHom_eq F _ (-q) h0]
  have hpre : pre F _ h0 = 0 := by
    funext v; apply Subtype.ext
    show (algebraMap F (FiniteAdeleRing (𝓞 F) F) (-q) + algebraMap F (FiniteAdeleRing (𝓞 F) F) q) v = _
    rw [(algebraMap F (FiniteAdeleRing (𝓞 F) F)).map_neg, neg_add_cancel]; rfl
  rw [hpre, (traceInt F).map_zero, sm_zero, (Algebra.trace ℚ F).map_neg,
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).map_neg, zero_sub, neg_neg]

private theorem traceFinHom_sm (w : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) :
    traceFinHom F (sm F w) = sm ℚ (traceInt F w) := by
  have h0 : algebraMap F (FiniteAdeleRing (𝓞 F) F) 0 + sm F w ∈ integralFiniteAdeles (𝓞 F) F := by
    rw [(algebraMap F (FiniteAdeleRing (𝓞 F) F)).map_zero, zero_add]; exact sm_mem F w
  rw [traceFinHom_eq F _ 0 h0]
  have hpre : pre F _ h0 = w := by
    funext v; apply Subtype.ext
    show (algebraMap F (FiniteAdeleRing (𝓞 F) F) 0 + sm F w) v = (w v : v.adicCompletion F)
    rw [(algebraMap F (FiniteAdeleRing (𝓞 F) F)).map_zero, zero_add]; rfl
  rw [hpre, (Algebra.trace ℚ F).map_zero, (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).map_zero, sub_zero]

theorem traceFinHom_structureMap (w : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) :
    traceFinHom F (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite w)
      = RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
        (fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) Filter.cofinite (traceInt F w) :=
  traceFinHom_sm F w

theorem continuous_traceFinHom : Continuous (traceFinHom F) := by
  apply continuous_of_continuousAt_zero
  rw [ContinuousAt, (traceFinHom F).map_zero]
  have hopen : ∀ v : HeightOneSpectrum (𝓞 F), IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => Valued.isOpen_valuationSubring _
  have h0 : (0 : FiniteAdeleRing (𝓞 F) F) = sm F 0 := (sm_zero F).symm
  have hnhds : 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) = Filter.map (sm F) (𝓝 0) := by
    rw [h0]
    exact RestrictedProduct.nhds_zero_eq_map_structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (B := fun v => v.adicCompletionIntegers F) hopen
  rw [hnhds, Filter.tendsto_map'_iff]
  have : (traceFinHom F) ∘ sm F = sm ℚ ∘ traceInt F := funext fun w => traceFinHom_sm F w
  rw [this]
  have hc : Continuous (sm ℚ ∘ traceInt F) := (continuous_sm ℚ).comp (continuous_traceInt F)
  have h00 : (sm ℚ ∘ traceInt F) 0 = 0 := by
    show sm ℚ (traceInt F 0) = 0
    rw [(traceInt F).map_zero, sm_zero]
  have ht := hc.tendsto 0
  rwa [h00] at ht

def adelicTraceData : AdelicTraceData F :=
  archTraceDataOf F (traceFinHom F) (traceFinHom_algebraMap F) (continuous_traceFinHom F)

abbrev stdAddChar : AddChar (AdeleRing (𝓞 F) F) ℂ := (adelicTraceData F).psiK

end FiniteTrace

end

end NumberField.StandardAddChar
