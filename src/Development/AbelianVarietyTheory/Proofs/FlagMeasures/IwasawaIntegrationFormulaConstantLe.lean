module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAlgebrasMaxCompactAndLeviInterStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAlgebraIsotropicFlagSelfAdjointLeviStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNilpotentAlgebraIsotropicFlagUnipotentRadiStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeWholeGroupStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRiemannianHaarUnitaryJSubgroupOfAlgebraStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureMatrixAlgebraSubgroupLocalAsymptoticStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeUnitaryMaximalCompactEqProdStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeMaximalCompactInterIsotropicFlagLeviStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaLieAlgebrasRelativePositionStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaGaugeDefiniteAndUnitBodyVolumeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagDimensionCountStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaLintegralUnfoldCompactLeviStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightInvariantEqSmulLeftInvariantProbabilityStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoProdGaugeMeasuresGaugeBodyStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaProductGaugeSandwichNearOneStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoSmallBallDensityOfSqueeze
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNearestPointCosetOrthogonalLieAlgebraStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutOutSubgroupTangentSecondOrderHilbertSchmidtStatement

public section

open Filter Set Topology

namespace IwasawaPilot

/-- Multiplying a lower small-ball density bound permits an extended-real coefficient. -/
private theorem lowerSmallBallDensity_mul {d : ℕ} {A : ENNReal} (c : ENNReal) (f : ℝ → ENNReal)
    (hf : ∀ a < A, ∀ᶠ r in 𝓝[>] 0, a < f r / ENNReal.ofReal (r ^ d)) :
    ∀ a < c * A, ∀ᶠ r in 𝓝[>] 0, a < c * f r / ENNReal.ofReal (r ^ d) := by
  have hA : (⨆ a : Iio A, a.val) = A := by
    apply Order.IsSuccPrelimit.iSup_Iio
    rw [Order.isSuccPrelimit_iff_forall_lt_nonempty_Ioo]
    intro a ha
    obtain ⟨b, hab, hbA⟩ := exists_between ha
    exact ⟨b, hab, hbA⟩
  intro a ha
  rw [← hA, ENNReal.mul_iSup, lt_iSup_iff] at ha
  obtain ⟨b, hb⟩ := ha
  filter_upwards [hf b.val b.property] with r hr
  rw [mul_div_assoc]
  exact hb.trans_le (by gcongr)

/-- One-sided comparison permits a different approximating family for each dilation. -/
private theorem smallBallDensity_le_of_dilation (d : ℕ) (A B : ENNReal)
    (hB : B ≠ ⊤) (b : ℝ → ENNReal) (f : ℝ → ℝ → ENNReal)
    (hb : Tendsto (fun r => b r / ENNReal.ofReal (r ^ d)) (𝓝[>] 0) (𝓝 B))
    (hf : ∀ η > 0, ∀ a < A, ∀ᶠ r in 𝓝[>] 0, a < f η r / ENNReal.ofReal (r ^ d))
    (hcompare : ∀ η > 0, ∀ᶠ r in 𝓝[>] 0, f η r ≤ b ((1 + η) * r)) : A ≤ B := by
  have hpow : Tendsto (fun η : ℝ => ENNReal.ofReal ((1 + η) ^ d)) (𝓝[>] 0) (𝓝 1) := by
    have h : Continuous (fun η : ℝ => ENNReal.ofReal ((1 + η) ^ d)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlimit : Tendsto (fun η : ℝ => ENNReal.ofReal ((1 + η) ^ d) * B) (𝓝[>] 0) (𝓝 B) := by
    simpa using ENNReal.Tendsto.mul_const (b := B) hpow (Or.inr hB)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlimit
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hη' : 0 < η := hη
  have hs : 0 < 1 + η := by linarith
  have hscale : Tendsto (fun r : ℝ => (1 + η) * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Continuous (fun r : ℝ => (1 + η) * r) := by fun_prop
      simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hs hr
  have hd : ENNReal.ofReal ((1 + η) ^ d) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hs d)).ne'
  let upper (r : ℝ) := ENNReal.ofReal ((1 + η) ^ d) *
    (b ((1 + η) * r) / ENNReal.ofReal (((1 + η) * r) ^ d))
  have hupper : Tendsto upper (𝓝[>] 0) (𝓝 (ENNReal.ofReal ((1 + η) ^ d) * B)) :=
    ENNReal.Tendsto.const_mul (hb.comp hscale) (Or.inr ENNReal.ofReal_ne_top)
  have hbound : ∀ᶠ r in 𝓝[>] 0, f η r / ENNReal.ofReal (r ^ d) ≤ upper r := by
    filter_upwards [hcompare η hη'] with r hr
    dsimp only [upper]
    rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hs.le d), ← mul_div_assoc,
      ENNReal.mul_div_mul_left _ _ hd ENNReal.ofReal_ne_top]
    exact ENNReal.div_le_div_right hr _
  by_contra! h
  obtain ⟨a, hlu, hua⟩ := exists_between h
  rcases (((hf η hη' a hua).and hbound).and ((tendsto_order.1 hupper).2 a hlu)).exists with
    ⟨r, ⟨hlo, hle⟩, hhi⟩
  exact (hlo.trans_le hle).not_gt hhi


end IwasawaPilot

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

open Filter Topology

namespace GlobalTheory.IwConst


private theorem lower_lintegral_triple_eq {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ₁ : Measure α) (μ₂ : Measure β) (μ₃ : Measure γ) [SFinite μ₂] [SFinite μ₃]
    (δ : β → ENNReal) (hδ : Measurable δ) (P : α × β × γ → ENNReal) (hP : Measurable P) :
    ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, P (u, m, k) ∂μ₃ ∂μ₂ ∂μ₁ = ∫⁻ x, δ x.2.1 * P x ∂(μ₁.prod (μ₂.prod μ₃)) := by
  symm
  rw [lintegral_prod (fun x => δ x.2.1 * P x)
    (show Measurable fun x : α × β × γ => δ x.2.1 * P x from (hδ.comp measurable_snd.fst).mul hP).aemeasurable]
  refine lintegral_congr fun u => ?_
  rw [lintegral_prod (fun y => δ y.1 * P (u, y))
    (show Measurable fun y : β × γ => δ y.1 * P (u, y) from
      (hδ.comp measurable_fst).mul (hP.comp measurable_prodMk_left)).aemeasurable]
  refine lintegral_congr fun m => ?_
  exact lintegral_const_mul (δ m)
    (show Measurable fun k : γ => P (u, m, k) from hP.comp (measurable_prodMk_left.comp measurable_prodMk_left))

private theorem IsCut.lower_sigmaFinite {n d : ℕ} {ε : Fin n → Bool} {S : Set (Formalism.REAL.UJ ε)}
    {E : Fin d → Matrix (Fin n) (Fin n) ℂ} (h : IsCut ε S E) {μ : Measure (Formalism.REAL.UJ ε)}
    (hμ : IsGaugeSub S d μ) : SigmaFinite μ := by
  obtain ⟨A, hA, hON, hspan, rfl⟩ := h
  exact (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hON hspan μ hμ).1


private theorem eventually_lt_div_pow_of_lower_squeeze (f : ℝ → ENNReal) (d : ℕ)
    (v : ENNReal) (hv : v ≠ ⊤)
    (h : ∀ η : ℝ, 0 < η → ∃ b : ℝ → ENNReal,
      Tendsto (fun r : ℝ => b r / ENNReal.ofReal (r ^ d)) (𝓝[>] (0 : ℝ)) (𝓝 v) ∧
      ∀ᶠ r in 𝓝[>] (0 : ℝ), b (r / (1 + η)) ≤ ENNReal.ofReal (1 + η) * f r) :
    ∀ b : ENNReal, b < v → ∀ᶠ r in 𝓝[>] (0 : ℝ), b < f r / ENNReal.ofReal (r ^ d) := by
  intro a ha
  have hg : ContinuousAt (fun η : ℝ => (1 + η)⁻¹ * ((1 + η)⁻¹) ^ d) 0 := by
    fun_prop (disch := norm_num)
  have hg0 : (fun η : ℝ => (1 + η)⁻¹ * ((1 + η)⁻¹) ^ d) 0 = 1 := by simp
  have hT := tendsto_ofReal_mul_of_one _ v hv hg hg0
  obtain ⟨η, hη, hηpos⟩ := ((tendsto_order.1 hT).1 a ha |>.and self_mem_nhdsWithin).exists
  have hη0 : (0 : ℝ) < η := hηpos
  have h1η : (0 : ℝ) < 1 + η := by linarith
  obtain ⟨b, hb, hev⟩ := h η hη0
  have hL := tendsto_scale_div_pow b d v ((1 + η)⁻¹) (inv_pos.2 h1η) ((1 + η)⁻¹)
    (inv_nonneg.2 h1η.le) hb hv
  filter_upwards [(tendsto_order.1 hL).1 a hη, hev] with r hr1 hr2
  refine lt_of_lt_of_le hr1 (ENNReal.div_le_div_right ?_ _)
  calc ENNReal.ofReal ((1 + η)⁻¹) * b ((1 + η)⁻¹ * r)
      ≤ ENNReal.ofReal ((1 + η)⁻¹) * (ENNReal.ofReal (1 + η) * f r) := by
        gcongr
        rw [← div_eq_inv_mul]
        exact hr2
    _ = f r := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 h1η.le), inv_mul_cancel₀ h1η.ne',
          ENNReal.ofReal_one, one_mul]

private theorem localised_iwasawa_lower_asymptotics (n : ℕ) (ε : Fin n → Bool) (a : ℕ)
    (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ))
    (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ)
    (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ)
    (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ) (hN : IsCut ε (flagN ε W) EN)
    (hM : IsCut ε (flagM ε W) EM) (hK : IsCut ε (maxK ε) EK) (hL : IsON EL)
    (hgau : ∀ v, gau EN EM EK EL v = 0 → v = 0) (hvol : volume {v | gau EN EM EK EL v ≤ 1} ≠ ⊤)
    (μN μM μK : Measure (Formalism.REAL.UJ ε)) (hμN : IsGaugeSub (flagN ε W) dN μN)
    (hμM : IsGaugeSub (flagM ε W) dM μM) (hμK : IsGaugeSub (maxK ε) dK μK)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ b : ENNReal, b < volume {v | gau EN EM EK EL v ≤ 1} →
      ∀ᶠ r in 𝓝[>] (0 : ℝ), b <
        (∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) *
          (slab ε EL ρ r).indicator 1 k ∂μK ∂μM ∂μN) / ENNReal.ofReal (r ^ (dN + (dM + dK))) := by
  have := hN.lower_sigmaFinite hμN
  have := hM.lower_sigmaFinite hμM
  have := hK.lower_sigmaFinite hμK
  obtain ⟨_, _, hCη⟩ := GlobalTheory.T.iwasawa_product_gauge_sandwich_near_one n ε _ _ _ dN dM dK dL EN EM EK EL hN hM hK hL hgau
  obtain ⟨t₀, ht₀, hasym⟩ :=
    GlobalTheory.T.tendsto_prod_gaugeMeasures_gaugeBody n ε _ _ _ dN dM dK dL EN EM EK EL hN hM hK hgau μN μM μK hμN hμM hμK
  obtain ⟨hdltm, -, hdlt⟩ := GlobalTheory.T.leviFactorInverseModulus_properties n ε a j W

  have hae : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.1 ∈ flagN ε W ∧ x.2.1 ∈ flagM ε W ∧ x.2.2 ∈ maxK ε := by
    have h1 : (μN.prod (μM.prod μK)) ((flagN ε W)ᶜ ×ˢ Set.univ) = 0 := by
      rw [Measure.prod_prod, hμN.1, zero_mul]
    have h2 : (μN.prod (μM.prod μK)) (Set.univ ×ˢ ((flagM ε W)ᶜ ×ˢ Set.univ)) = 0 := by
      rw [Measure.prod_prod, Measure.prod_prod, hμM.1, zero_mul, mul_zero]
    have h3 : (μN.prod (μM.prod μK)) (Set.univ ×ˢ (Set.univ ×ˢ (maxK ε)ᶜ)) = 0 := by
      rw [Measure.prod_prod, Measure.prod_prod, hμK.1, mul_zero, mul_zero]
    have e1 : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.1 ∈ flagN ε W := by
      rw [ae_iff]
      exact measure_mono_null (fun x hx => Set.mem_prod.2 ⟨hx, Set.mem_univ _⟩) h1
    have e2 : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.2.1 ∈ flagM ε W := by
      rw [ae_iff]
      exact measure_mono_null
        (fun x hx => Set.mem_prod.2 ⟨Set.mem_univ _, Set.mem_prod.2 ⟨hx, Set.mem_univ _⟩⟩) h2
    have e3 : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.2.2 ∈ maxK ε := by
      rw [ae_iff]
      exact measure_mono_null
        (fun x hx => Set.mem_prod.2 ⟨Set.mem_univ _, Set.mem_prod.2 ⟨Set.mem_univ _, hx⟩⟩) h3
    filter_upwards [e1, e2, e3] with x hx1 hx2 hx3
    exact ⟨hx1, hx2, hx3⟩
  have hPmeas : ∀ r : ℝ, Measurable fun x : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε × Formalism.REAL.UJ ε =>
      (hsBall ε r).indicator (1 : Formalism.REAL.UJ ε → ENNReal) (x.1 * x.2.1 * x.2.2) *
        (slab ε EL ρ r).indicator 1 x.2.2 := by
    intro r
    exact ((measurable_one.indicator (measurableSet_hsBall ε r)).comp
      ((measurable_fst.mul measurable_snd.fst).mul measurable_snd.snd)).mul
      ((measurable_one.indicator (measurableSet_slab ε EL ρ r)).comp measurable_snd.snd)

  have hF : ∀ r : ℝ, (∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) *
      (slab ε EL ρ r).indicator 1 k ∂μK ∂μM ∂μN) =
      ∫⁻ x, dlt j W x.2.1 * ((hsBall ε r).indicator 1 (x.1 * x.2.1 * x.2.2) *
        (slab ε EL ρ r).indicator 1 x.2.2) ∂(μN.prod (μM.prod μK)) := fun r =>
    lower_lintegral_triple_eq μN μM μK (dlt j W) hdltm
      (fun x => (hsBall ε r).indicator 1 (x.1 * x.2.1 * x.2.2) *
        (slab ε EL ρ r).indicator 1 x.2.2) (hPmeas r)
  have hc := continuous_nrm_uMat ε
  refine eventually_lt_div_pow_of_lower_squeeze _ (dN + (dM + dK)) _ hvol ?_
  intro η hη
  obtain ⟨t₂, ht₂, h₂⟩ := hCη η hη
  obtain ⟨t₃, ht₃, h₃⟩ := hdlt η hη
  obtain ⟨t, ht, htt₀, htρ, htt₂, htt₃⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ t₀ ∧ t ≤ ρ ∧ t ≤ t₂ ∧ t ≤ t₃ :=
    ⟨min (min t₀ ρ) (min t₂ t₃), lt_min (lt_min ht₀ hρ) (lt_min ht₂ ht₃),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hBmeas : ∀ s : ℝ, MeasurableSet {x : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε × Formalism.REAL.UJ ε |
      (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧
        gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ s} := by
    intro s
    refine measurableSet_setOfPred.2
      (((measurableSet_setOfPred.1 (measurableSet_lt (hc.measurable.comp measurable_fst) measurable_const)).and
      ((measurableSet_setOfPred.1 (measurableSet_lt (hc.measurable.comp measurable_snd.fst) measurable_const)).and
        (measurableSet_setOfPred.1 (measurableSet_lt (hc.measurable.comp measurable_snd.snd) measurable_const)))).and
      (measurableSet_setOfPred.1 (measurableSet_le ?_ measurable_const)))
    exact (continuous_gau EN EM EK EL).measurable.comp
      (((continuous_crd_uMat ε EN).measurable.comp measurable_fst).prodMk
        (((continuous_crd_uMat ε EM).measurable.comp measurable_snd.fst).prodMk
          ((continuous_crd_uMat ε EK).measurable.comp measurable_snd.snd)))
  refine ⟨fun s => (μN.prod (μM.prod μK)) {x |
      (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧
        gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ s},
    hasym t ht htt₀, ?_⟩
  refine Filter.Eventually.of_forall (fun r => ?_)
  have hη1 : (0 : ℝ) < 1 + η := by linarith
  rw [hF r]
  dsimp only
  rw [← lintegral_indicator_one (hBmeas _), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [hae] with x hx
  obtain ⟨hxN, hxM, hxK⟩ := hx
  rw [Set.indicator_apply]
  split_ifs with hB
  · obtain ⟨⟨hu, hm, hk⟩, hγ⟩ := hB
    obtain ⟨-, hσγ, -, -, -⟩ := h₂ x.1 hxN x.2.1 hxM x.2.2 hxK (lt_of_lt_of_le hu htt₂)
      (lt_of_lt_of_le hm htt₂) (lt_of_lt_of_le hk htt₂) _ _ rfl rfl
    have hσ : max (nrm (uMat (x.1 * x.2.1 * x.2.2) - 1)) (len (crd EL (uMat x.2.2 - 1))) ≤ r := by
      refine hσγ.trans ?_
      calc (1 + η) * gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1),
            crd EK (uMat x.2.2 - 1)) ≤ (1 + η) * (r / (1 + η)) :=
            mul_le_mul_of_nonneg_left hγ hη1.le
        _ = r := by field_simp
    have hmem1 : x.1 * x.2.1 * x.2.2 ∈ hsBall ε r :=
      ((le_max_left _ _).trans hσ : nrm (uMat (x.1 * x.2.1 * x.2.2) - 1) ≤ r)
    have hmem2 : x.2.2 ∈ slab ε EL ρ r :=
      (⟨lt_of_lt_of_le hk htρ, (le_max_right _ _).trans hσ⟩ :
        nrm (uMat x.2.2 - 1) < ρ ∧ len (crd EL (uMat x.2.2 - 1)) ≤ r)
    rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2]
    simp only [Pi.one_apply, mul_one]
    exact (h₃ x.2.1 hxM (lt_of_lt_of_le hm htt₃)).2
  · exact bot_le

end GlobalTheory.IwConst

open Filter MeasureTheory Matrix Topology
open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.IwConst

private theorem coefficient_slab_arith_lower {a s r t η u v : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hst : s < t) (hrt : r < t)
    (ht : t ≤ 1 / 24) (hη : 0 < η) (htη : 3 * t * (1 + η) ≤ η) (h1 : a < 1 / 8 + s + a * s)
    (h2 : a ≤ u + a ^ 2) (h3 : u ≤ v + a * s) (h4 : v ≤ r) : a ≤ (1 + η) * r := by

  have hs24 : s < 1 / 24 := lt_of_lt_of_le hst ht
  have hA : a < 4 / 23 := by nlinarith [mul_nonneg ha (sub_nonneg.2 hs24.le)]
  have hkey : a * (1 - s - a) ≤ r := by nlinarith
  have hgap : 433 / 552 ≤ 1 - s - a := by linarith
  have hat : a * (433 / 552) < t := by nlinarith [mul_le_mul_of_nonneg_left hgap ha]
  have hsum : (1 + η) * (s + a) ≤ η := by
    nlinarith [mul_le_mul_of_nonneg_left (show s + a ≤ 3 * t by linarith) (show (0 : ℝ) ≤ 1 + η by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hkey (show (0 : ℝ) ≤ 1 + η by linarith),
    mul_le_mul_of_nonneg_left hsum ha]

private theorem slab_mem_to_ball_of_orthogonal {n d : ℕ} {ε : Fin n → Bool}
    {S : Set (Formalism.REAL.UJ ε)} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}
    (hS : IsCut ε S E) {ρ r η : ℝ} (hρ : ρ ≤ 1 / 24) (hr : r < ρ) (hη : 0 < η)
    (hρη : 3 * ρ * (1 + η) ≤ η) {k l : Formalism.REAL.UJ ε}
    (hk : nrm (uMat k - 1) < ρ) (hk0 : crd E (uMat k - 1) = 0)
    (hl : l ∈ S) (hslab : l * k ∈ slab ε E ρ r) :
    l ∈ hsBall ε ((1 + η) * r) := by
  obtain ⟨hZ, hv⟩ := hslab
  show nrm (uMat l - 1) ≤ (1 + η) * r
  have hON := hS.isON
  have hmul : uMat (l * k) - 1 = (uMat l - 1) + (uMat k - 1) + (uMat l - 1) * (uMat k - 1) := by
    have e : uMat (l * k) = uMat l * uMat k := rfl
    rw [e]; noncomm_ring
  have hXY := nrm_mul_le (uMat l - 1) (uMat k - 1)
  have hX : uMat l - 1 = (uMat (l * k) - 1) - (uMat k - 1) - (uMat l - 1) * (uMat k - 1) := by
    rw [hmul]; abel
  have h1 : nrm (uMat l - 1) < 1 / 8 + nrm (uMat k - 1) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
    have e := nrm_sub_le ((uMat (l * k) - 1) - (uMat k - 1)) ((uMat l - 1) * (uMat k - 1))
    have e' := nrm_sub_le (uMat (l * k) - 1) (uMat k - 1)
    rw [← hX] at e
    linarith
  have h2 : nrm (uMat l - 1) ≤ len (crd E (uMat l - 1)) + nrm (uMat l - 1) ^ 2 := by
    have hp := GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt n ε S d E hS l hl
    have e := nrm_add_le (cmb E (crd E (uMat l - 1))) (uMat l - 1 - cmb E (crd E (uMat l - 1)))
    rw [add_sub_cancel, nrm_cmb hON] at e
    linarith
  have h3 : len (crd E (uMat l - 1)) ≤
      len (crd E (uMat (l * k) - 1)) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
    have hc : crd E (uMat l - 1) =
        crd E (uMat (l * k) - 1) + -crd E ((uMat l - 1) * (uMat k - 1)) := by
      conv_lhs => rw [hX]
      rw [crd_sub, crd_sub, hk0, sub_zero, sub_eq_add_neg]
    rw [hc]
    refine le_trans (len_add_le _ _) (add_le_add le_rfl ?_)
    rw [len_neg]
    exact le_trans (len_crd_le hON _) hXY
  exact coefficient_slab_arith_lower (nrm_nonneg _) (nrm_nonneg _) hk hr hρ hη hρη h1 h2 h3 hv

private theorem slab_fibre_measure_le {n d : ℕ} {ε : Fin n → Bool}
    {S : Set (Formalism.REAL.UJ ε)} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}
    (hS : IsCut ε S E) (hSK : S ⊆ maxK ε) (hskew : ∀ i, (E i)ᴴ = -E i)
    (ν : Measure (Formalism.REAL.UJ ε)) (hν : ν Sᶜ = 0)
    (hinv : ∀ l ∈ S, ν.map (fun g => g * l) = ν) {ρ r η : ℝ}
    (hρ : ρ ≤ 1 / 24) (hr : r < ρ) (hη : 0 < η) (hρη : 3 * ρ * (1 + η) ≤ η)
    {k : Formalism.REAL.UJ ε} (hk : k ∈ maxK ε) :
    ν {l | l * k ∈ slab ε E ρ r} ≤ ν (hsBall ε ((1 + η) * r)) := by
  have hsupp : ∀ᵐ l ∂ν, l ∈ S := mem_ae_iff.2 hν
  by_cases h : ∃ l ∈ S, l * k ∈ slab ε E ρ r
  · obtain ⟨l0, hl0, hslab0⟩ := h
    obtain ⟨l1, hl1, h0, hminimal⟩ :=
      GlobalTheory.T.exists_nearest_point_coset_orthogonal_lieAlgebra n ε S d E hS hSK hskew k hk
    have hclose := (hminimal l0 hl0).trans_lt hslab0.1
    calc
      ν {l | l * k ∈ slab ε E ρ r} =
          (ν.map (fun g => g * l1)) {l | l * k ∈ slab ε E ρ r} := by
        rw [hinv l1 hl1]
      _ = ν ((fun g => g * l1) ⁻¹' {l | l * k ∈ slab ε E ρ r}) :=
        (Homeomorph.mulRight l1).toMeasurableEquiv.map_apply _
      _ = ν {l | l * (l1 * k) ∈ slab ε E ρ r} := by
        congr 1
        ext l
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, mul_assoc]
      _ ≤ _ := measure_mono_ae <| by
        filter_upwards [hsupp] with l hl
        exact slab_mem_to_ball_of_orthogonal hS hρ hr hη hρη hclose h0 hl
  · calc
      _ ≤ ν (∅ : Set (Formalism.REAL.UJ ε)) := measure_mono_ae <| by
        filter_upwards [hsupp] with l hl
        exact fun hl' => (h ⟨l, hl, hl'⟩).elim
      _ ≤ _ := by simp

end GlobalTheory.IwConst

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.IwConst

open Filter Topology

private theorem coefficient_triple_mono {G : Type} [MeasurableSpace G] {N M K : Set G} {μN μM μK : Measure G} (hN : μN Nᶜ = 0)
    (hM : μM Mᶜ = 0) (hK : μK Kᶜ = 0) (δ : G → ENNReal) {F F' : G → G → G → ENNReal}
    (h : ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, F u m k ≤ F' u m k) :
    ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F u m k ∂μK ∂μM ∂μN ≤ ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F' u m k ∂μK ∂μM ∂μN := by
  refine lintegral_mono_ae ?_
  filter_upwards [show N ∈ ae μN from mem_ae_iff.mpr hN] with u hu
  refine lintegral_mono_ae ?_
  filter_upwards [show M ∈ ae μM from mem_ae_iff.mpr hM] with m hm
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine lintegral_mono_ae ?_
  filter_upwards [show K ∈ ae μK from mem_ae_iff.mpr hK] with k hk
  exact h u hu m hm k hk

private theorem coefficient_triple_const {G : Type} [MeasurableSpace G] (μN μM μK : Measure G) (δ : G → ENNReal)
    (F : G → G → G → ENNReal) {V β : ENNReal} (hV : V ≠ ⊤) (hβ : β ≠ ⊤) :
    ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F u m k * β ∂(V • μK) ∂μM ∂μN =
      V * β * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F u m k ∂μK ∂μM ∂μN := by
  have hVβ : V * β ≠ ⊤ := ENNReal.mul_ne_top hV hβ
  simp_rw [lintegral_smul_measure, smul_eq_mul, lintegral_mul_const' _ _ hβ]
  have key : ∀ u m, δ m * (V * ((∫⁻ k, F u m k ∂μK) * β)) = V * β * (δ m * ∫⁻ k, F u m k ∂μK) := by
    intro u m; ring
  simp_rw [key, lintegral_const_mul' _ _ hVβ]

private theorem coefficient_ballVol_ne_zero (d : ℕ) : ballVol d ≠ 0 := by
  unfold ballVol
  exact (Metric.measure_ball_pos _ _ one_pos).ne'

private theorem coefficient_ballVol_ne_top (d : ℕ) : ballVol d ≠ ⊤ := by
  unfold ballVol
  exact measure_ball_lt_top.ne

private theorem coefficient_volU_pos' (i : ℕ) : 0 < volU i := by
  unfold volU sphV
  refine mul_pos (Finset.prod_pos fun l _ => ?_) (by positivity)
  positivity

private theorem coefficient_tendsto_mul_balls {f g : ℝ → ENNReal} {d e : ℕ} {V : ENNReal} (hV : V ≠ ⊤)
    (hf : Tendsto (fun r : ℝ => f r / ENNReal.ofReal (r ^ d)) (𝓝[>] 0) (𝓝 (ballVol d)))
    (hg : Tendsto (fun r : ℝ => g r / ENNReal.ofReal (r ^ e)) (𝓝[>] 0) (𝓝 (ballVol e))) :
    Tendsto (fun r : ℝ => V * f r * g r / ENNReal.ofReal (r ^ (d + e))) (𝓝[>] 0)
      (𝓝 (V * (ballVol d * ballVol e))) := by
  have hlim : Tendsto (fun r : ℝ => V * ((f r / ENNReal.ofReal (r ^ d)) * (g r / ENNReal.ofReal (r ^ e))))
      (𝓝[>] 0) (𝓝 (V * (ballVol d * ballVol e))) :=
    ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.mul hf (Or.inr (coefficient_ballVol_ne_top e)) hg (Or.inr (coefficient_ballVol_ne_top d))) (Or.inr hV)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : (0 : ℝ) ≤ r := le_of_lt hr
  rw [pow_add, ENNReal.ofReal_mul (pow_nonneg hr' _), div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top)]
  ring

private theorem hs_conjTranspose_mul_mul_of_unitary {n : ℕ} (U X : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) :
    Formalism.REAL.hs (Uᴴ * X * U) = Formalism.REAL.hs X := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have key : ∀ Y : Matrix (Fin n) (Fin n) ℂ, ((Formalism.REAL.hs Y : ℝ) : ℂ) = (Y * Yᴴ).trace := by
    intro Y
    simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  have h1 : ((Formalism.REAL.hs (Uᴴ * X * U) : ℝ) : ℂ) = ((Formalism.REAL.hs X : ℝ) : ℂ) := by
    rw [key, key, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hU', Matrix.one_mul, Matrix.trace_mul_comm, Matrix.mul_assoc,
      Matrix.mul_assoc, hU', Matrix.mul_one]
  exact_mod_cast h1

private theorem map_mul_right_eq_of_isGaugeSub {n : ℕ} {ε : Fin n → Bool} (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    {d : ℕ} (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hAE : ∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E))
    (μ : Measure (Formalism.REAL.UJ ε)) (hμ : IsGaugeSub {g | uMat g - 1 ∈ A} d μ)
    (l : Formalism.REAL.UJ ε) (hl : uMat l - 1 ∈ A) (hu : (uMat l)ᴴ * uMat l = 1) :
    μ.map (fun g => g * l) = μ := by
  have huniq := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hE hAE μ hμ).2.2.1
  have hcut : IsCut ε {g | uMat g - 1 ∈ A} E := ⟨A, hA, hE, hAE, rfl⟩
  obtain ⟨H, hH, -⟩ := hcut.subgroup
  have hlH : l ∈ H := by rw [← SetLike.mem_coe, hH]; exact hl
  have hlinv : l⁻¹ ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ A} := by
    rw [← hH]; exact H.inv_mem hlH
  have hinvU : uMat l⁻¹ = (uMat l)ᴴ := by
    have h1 : uMat l⁻¹ * uMat l = 1 := by simp [uMat]
    calc uMat l⁻¹ = uMat l⁻¹ * (uMat l * (uMat l)ᴴ) := by rw [mul_eq_one_comm.mp hu, Matrix.mul_one]
      _ = (uMat l)ᴴ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  apply huniq
  obtain ⟨h0, hinv, hlim⟩ := hμ
  have he : (fun g : Formalism.REAL.UJ ε => g * l) = ⇑(MeasurableEquiv.mulRight l) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [he, MeasurableEquiv.map_apply, ← hH]
    have hpre : ⇑(MeasurableEquiv.mulRight l) ⁻¹' (↑H)ᶜ = (↑H : Set (Formalism.REAL.UJ ε))ᶜ := by
      ext g
      simp [H.mul_mem_cancel_right hlH]
    rw [hpre, hH]
    exact h0
  · intro s hs
    rw [Measure.map_map (measurable_const_mul s) (measurable_mul_const l),
      show ((fun g => s * g) ∘ fun g => g * l) = (fun g => g * l) ∘ (fun g => s * g) by
        funext g; simp [mul_assoc],
      ← Measure.map_map (measurable_mul_const l) (measurable_const_mul s), hinv s hs]
  · refine hlim.congr (fun r => ?_)
    congr 1
    rw [he, MeasurableEquiv.map_apply]
    conv_rhs => rw [← hinv l⁻¹ hlinv]
    have he2 : (fun g : Formalism.REAL.UJ ε => l⁻¹ * g) = ⇑(MeasurableEquiv.mulLeft l⁻¹) := rfl
    rw [he2, MeasurableEquiv.map_apply]
    congr 1
    ext g
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, MeasurableEquiv.coe_mulRight, MeasurableEquiv.coe_mulLeft]
    have hg : uMat (l⁻¹ * g * l) - 1 = (uMat l)ᴴ * (uMat g - 1) * uMat l := by
      rw [show uMat (l⁻¹ * g * l) = uMat l⁻¹ * uMat g * uMat l by simp [uMat], hinvU]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hu]
    rw [hg, hs_conjTranspose_mul_mul_of_unitary _ _ hu]

private theorem lintegral_lintegral_mul_const {G : Type} [MeasurableSpace G] (μN μM μK : Measure G) (δ : G → ENNReal)
    (F : G → G → G → ENNReal) {β : ENNReal} (hβ : β ≠ ⊤) :
    ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F u m k * β ∂μK ∂μM ∂μN = β * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, F u m k ∂μK ∂μM ∂μN := by
  have h := coefficient_triple_const μN μM μK δ F (V := 1) ENNReal.one_ne_top hβ
  rw [one_smul, one_mul] at h
  exact h

private theorem lintegral_indicator_mul_right {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (ν : Measure G)
    {s : Set G} (hs : MeasurableSet s) (k : G) :
    ∫⁻ l, s.indicator 1 (l * k) ∂ν = ν {l | l * k ∈ s} := by
  have h := lintegral_indicator_one (μ := ν) (measurable_mul_const k hs)
  refine Eq.trans ?_ h
  congr 1

private theorem cancel_mul_right_le {x y t : ENNReal} (h0 : t ≠ 0) (ht : t ≠ ⊤)
    (h : x * t ≤ y * t) : x ≤ y := by
  calc
    x = (t * x) / (t * 1) := by rw [ENNReal.mul_div_mul_left _ _ h0 ht, div_one]
    _ ≤ (t * y) / (t * 1) := ENNReal.div_le_div_right (by simpa [mul_comm t] using h) _
    _ = y := by rw [ENNReal.mul_div_mul_left _ _ h0 ht, div_one]

theorem iwasawa_constant_le : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (μN μM μK : Measure (Formalism.REAL.UJ ε)), IsGaugeSub (flagN ε W) (dimN n j) μN → IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM → μK (maxK ε)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ maxK ε, μK.map (fun g => k * g) = μK) → ∀ (c : ℝ) (κ : ENNReal), IsGauge ε c → (∀ φ : Formalism.REAL.UJ ε → ENNReal, Measurable φ → ∫⁻ g, φ g ∂(Formalism.REAL.muG ε) = κ * ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) * ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN) → ENNReal.ofReal c * κ ≤ ENNReal.ofReal (cIw p q j) := by
  intro n ε p q hp hq a j hj W hW μN μM μK hN hM hK0 hK1 hKinv c κ hc hform
  obtain ⟨hpq, hn2, hdK⟩ := GlobalTheory.T.isotropicFlag_dimension_count n ε a j W hW p q hp hq
  obtain ⟨AN, EN, hAN, hEN, hAEN, hNset⟩ := GlobalTheory.T.exists_nilpotentAlgebra_isotropicFlagUnipotentRadical n ε a j W hW
  obtain ⟨AM, EM, hAM, hEM, hAEM, hMset⟩ := GlobalTheory.T.exists_algebra_isotropicFlagSelfAdjointLevi n ε a j W hW
  obtain ⟨⟨AK, EK, hAK, hEK, hAEK, hKset⟩, ⟨AL, EL, hAL, hEL, hAEL, hLset⟩⟩ :=
    GlobalTheory.T.exists_algebras_maxCompact_and_levi_inter n ε a j W hW p q hp hq
  have cN : IsCut ε (flagN ε W) EN := ⟨AN, hAN, hEN, hAEN, hNset⟩
  have cM : IsCut ε (flagM ε W) EM := ⟨AM, hAM, hEM, hAEM, hMset⟩
  have cK : IsCut ε (maxK ε) EK := ⟨AK, hAK, hEK, hAEK, hKset⟩
  have cL : IsCut ε (maxK ε ∩ flagM ε W) EL := ⟨AL, hAL, hEL, hAEL, hLset⟩
  have hrel := GlobalTheory.T.iwasawa_lieAlgebras_relative_position n ε a j W hW _ _ _ _ EN EM EK EL cN cM cK cL
  obtain ⟨hnd, hvol⟩ := GlobalTheory.T.iwasawaGauge_definite_and_unitBody_volume n _ _ _ _ EN EM EK EL cN.isON cM.isON cK.isON cL.isON hrel hdK

  have hN' : IsGaugeSub {g | uMat g - 1 ∈ AN} (dimN n j) μN := by rw [← hNset]; exact hN
  have hM' : IsGaugeSub {g | uMat g - 1 ∈ AM} ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μM := by
    rw [← hMset]; exact hM
  have : SigmaFinite μN := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε AN _ EN hAN hEN hAEN μN hN').1
  have : SigmaFinite μM := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε AM _ EM hAM hEM hAEM μM hM').1
  obtain ⟨νL, hνσ, hνL⟩ := GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra n ε AL _ EL hAL hEL hAEL
  have := hνσ
  have hνL' : IsGaugeSub (maxK ε ∩ flagM ε W) ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) νL := by
    rw [hLset]; exact hνL
  have : IsFiniteMeasureOnCompacts νL := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε AL _ EL hAL hEL hAEL νL hνL).2.1
  obtain ⟨μ0, hμ0σ, hμ0⟩ := GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra n ε AK _ EK hAK hEK hAEK
  have := hμ0σ
  have hμ0' : IsGaugeSub (maxK ε) (p ^ 2 + q ^ 2) μ0 := by rw [hKset]; exact hμ0
  have hVK := GlobalTheory.T.volume_unitaryMaximalCompact_eq_prod n ε p q hp hq μ0 hμ0'
  have hVL := GlobalTheory.T.volume_maximalCompact_inter_isotropicFlagLevi n ε p q hp hq a j W hW νL hνL'

  have rK : ∀ l ∈ maxK ε, μ0.map (fun g => g * l) = μ0 := fun l hl =>
    map_mul_right_eq_of_isGaugeSub AK EK hAK hEK hAEK μ0 hμ0 l (by
      have h : l ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ AK} := by rw [← hKset]; exact hl
      exact h) hl
  have rM : ∀ l ∈ maxK ε ∩ flagM ε W, μM.map (fun g => g * l) = μM := fun l hl =>
    map_mul_right_eq_of_isGaugeSub AM EM hAM hEM hAEM μM hM' l (by
      have h : l ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ AM} := by rw [← hMset]; exact hl.2
      exact h) hl.1
  have rL : ∀ l ∈ maxK ε ∩ flagM ε W, νL.map (fun g => g * l) = νL := fun l hl =>
    map_mul_right_eq_of_isGaugeSub AL EL hAL hEL hAEL νL hνL l (by
      have h : l ∈ {g : Formalism.REAL.UJ ε | uMat g - 1 ∈ AL} := by rw [← hLset]; exact hl
      exact h) hl.1
  have : IsProbabilityMeasure μK := ⟨hK1⟩
  have hμ0eq := GlobalTheory.T.right_invariant_eq_smul_left_invariant_probability (Formalism.REAL.UJ ε) (maxK ε) μK μ0 hK0 hμ0'.1 hK1 hKinv rK
  rw [hVK] at hμ0eq

  have hvpos : ∀ i, 0 < volU i := coefficient_volU_pos'
  have hVtop : ENNReal.ofReal (volU p * volU q) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hδ := GlobalTheory.T.leviFactorInverseModulus_properties n ε a j W
  have hΓtop : volume {v | gau EN EM EK EL v ≤ 1} ≠ ⊤ := by
    rw [hvol]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (coefficient_ballVol_ne_top _)) (coefficient_ballVol_ne_top _)
  obtain ⟨Fp, hFp⟩ : ∃ F : ℝ → ENNReal, F = fun r =>
      ∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) ∂μ0 ∂μM ∂μN := ⟨_, rfl⟩
  obtain ⟨Sp, hSp⟩ : ∃ F : ℝ → ℝ → ENNReal, F = fun ρ r =>
      ∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) * (slab ε EL ρ r).indicator 1 k
        ∂μ0 ∂μM ∂μN := ⟨_, rfl⟩
  have hBtop : ∀ s, νL (hsBall ε s) ≠ ⊤ := fun s => ((isCompact_hsBall ε s).measure_lt_top).ne

  have hFmono : ∀ s r, s ≤ r → Fp s ≤ Fp r := by
    intro s r hsr
    simp only [hFp]
    refine coefficient_triple_mono hN.1 hM.1 hμ0'.1 _ (fun u _ m _ k _ => ?_)
    refine Set.indicator_le_indicator_of_subset (fun g hg => ?_) (fun _ => by positivity) _
    exact (le_trans hg hsr : nrm (uMat g - 1) ≤ r)

  let ρ (η : ℝ) := min (1 / 24) (η / (3 * (1 + η)))
  have hρpos (η : ℝ) (hη : 0 < η) : 0 < ρ η :=
    lt_min (by norm_num) (div_pos hη (by positivity))
  have hsand (η : ℝ) (hη : 0 < η) : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      νL Set.univ * Sp (ρ η) r ≤ νL (hsBall ε ((1 + η) * r)) * Fp r := by
    have hρle : ρ η ≤ 1 / 24 := min_le_left _ _
    have hρη : 3 * ρ η * (1 + η) ≤ η := by
      have hden : 0 < 3 * (1 + η) := by positivity
      calc
        3 * ρ η * (1 + η) = ρ η * (3 * (1 + η)) := by ring
        _ ≤ η := (le_div_iff₀ hden).mp (min_le_right _ _)
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ρ η :=
      nhdsWithin_le_nhds (Iio_mem_nhds (hρpos η hη))
    filter_upwards [hev] with r hr
    have hswap := GlobalTheory.T.iwasawa_lintegral_unfold_compact_levi
      (Formalism.REAL.UJ ε) (flagM ε W) (maxK ε ∩ flagM ε W) μN μM μ0 νL (dlt j W)
      ((hsBall ε r).indicator 1) ((slab ε EL (ρ η) r).indicator 1) hδ.1
      (measurable_one.indicator (measurableSet_hsBall ε r))
      (measurable_one.indicator (measurableSet_slab ε EL (ρ η) r))
      hM.1 hνL'.1 rM (fun l hl => hμ0'.2.1 l hl.1) hδ.2.1
    simp only [hSp, hFp]
    rw [hswap, ← lintegral_lintegral_mul_const _ _ _ _ _ (hBtop _)]
    refine coefficient_triple_mono hN.1 hM.1 hμ0'.1 _ (fun u _ m _ k hk => ?_)
    by_cases hmem : u * m * k ∈ hsBall ε r
    · rw [Set.indicator_of_mem hmem,
        lintegral_indicator_mul_right νL (measurableSet_slab ε EL (ρ η) r)]
      simp only [Pi.one_apply, one_mul]
      exact slab_fibre_measure_le cL (fun _ hl => hl.1) hrel.2.2.2.2.2.1
        νL hνL'.1 rL hρle hr hη hρη hk
    · simp [hmem]

  have hf : Tendsto (fun r : ℝ => ENNReal.ofReal c * Formalism.REAL.muG ε (hsBall ε r) / ENNReal.ofReal (r ^ (n ^ 2)))
      (𝓝[>] 0) (𝓝 (ballVol (n ^ 2))) := by
    have h3 := ((GlobalTheory.T.riemannianHaarGauge_whole_group n ε).1 c hc).2.2.2
    refine h3.congr (fun r => ?_)
    rw [smul_apply, smul_eq_mul]
    rfl
  have hg : Tendsto (fun r : ℝ => νL (hsBall ε r) /
      ENNReal.ofReal (r ^ ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2))) (𝓝[>] 0)
      (𝓝 (ballVol ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2))) := hνL'.2.2
  have hFK : ∀ r, Fp r = ENNReal.ofReal (volU p * volU q) *
      ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) *
        ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) ∂μK ∂μM ∂μN := by
    intro r
    have h := coefficient_triple_const μN μM μK (dlt j W) (fun u m k => (hsBall ε r).indicator 1 (u * m * k)) hVtop
      ENNReal.one_ne_top
    simp only [mul_one] at h
    simp only [hFp]
    rw [hμ0eq, h]
    rfl
  have hmuG : ∀ r, Formalism.REAL.muG ε (hsBall ε r) = κ *
      ∫⁻ u, ∫⁻ m, ENNReal.ofReal (layerProd n 1 j (locSize j W (uMat m)) id) *
        ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) ∂μK ∂μM ∂μN := by
    intro r
    rw [← hform _ (measurable_one.indicator (measurableSet_hsBall ε r)), lintegral_indicator_one
      (measurableSet_hsBall ε r)]
  have hb : Tendsto (fun r : ℝ => ENNReal.ofReal c * κ * (Fp r * νL (hsBall ε r)) /
      ENNReal.ofReal (r ^ (n ^ 2 + ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (volU p * volU q) * (ballVol (n ^ 2) *
        ballVol ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2)))) := by
    refine (coefficient_tendsto_mul_balls hVtop hf hg).congr (fun r => ?_)
    rw [hFK, hmuG]
    congr 1
    ring
  have hvtop : ENNReal.ofReal (volU p * volU q) * (ballVol (n ^ 2) *
      ballVol ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top hVtop (ENNReal.mul_ne_top (coefficient_ballVol_ne_top _) (coefficient_ballVol_ne_top _))
  have hexp : dimN n j + ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2 + (p ^ 2 + q ^ 2)) =
      n ^ 2 + ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) := by
    rw [hdK, hn2]; ring
  have hle : ENNReal.ofReal c * κ * (νL Set.univ * volume {v | gau EN EM EK EL v ≤ 1}) ≤
      ENNReal.ofReal (volU p * volU q) * (ballVol (n ^ 2) *
        ballVol ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2)) := by
    refine IwasawaPilot.smallBallDensity_le_of_dilation _ _ _ hvtop
      (fun r => ENNReal.ofReal c * κ * (Fp r * νL (hsBall ε r)))
      (fun η r => ENNReal.ofReal c * κ * (νL Set.univ * Sp (ρ η) r)) hb ?_ ?_
    · intro η hη
      have hlower := localised_iwasawa_lower_asymptotics n ε a j W _ _ _ _ EN EM EK EL
        cN cM cK cL.isON hnd hΓtop μN μM μ0 hN hM hμ0' (ρ η) (hρpos η hη)
      rw [← hexp]
      simpa only [mul_assoc] using
        IwasawaPilot.lowerSmallBallDensity_mul (ENNReal.ofReal c * κ * νL Set.univ)
          (Sp (ρ η)) (by simpa only [hSp] using hlower)
    · intro η hη
      filter_upwards [hsand η hη, self_mem_nhdsWithin] with r hr hr0
      have hscale : r ≤ (1 + η) * r := by
        have hr0' : 0 < r := hr0
        nlinarith
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc
        νL Set.univ * Sp (ρ η) r ≤ νL (hsBall ε ((1 + η) * r)) * Fp r := hr
        _ ≤ νL (hsBall ε ((1 + η) * r)) * Fp ((1 + η) * r) :=
          mul_le_mul_of_nonneg_left (hFmono _ _ hscale) (by positivity)
        _ = _ := mul_comm _ _

  rw [hvol, hVL, ← hn2] at hle
  have hB0 : ballVol (n ^ 2) * ballVol ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) ≠ 0 :=
    mul_ne_zero (coefficient_ballVol_ne_zero _) (coefficient_ballVol_ne_zero _)
  have hBt : ballVol (n ^ 2) * ballVol ((p - ∑ i, j i) ^ 2 + (q - ∑ i, j i) ^ 2 + ∑ i, j i ^ 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (coefficient_ballVol_ne_top _) (coefficient_ballVol_ne_top _)
  have hAL : 0 < (∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) * volU (p - ∑ i, j i) *
      volU (q - ∑ i, j i) :=
    mul_pos (mul_pos (Finset.prod_pos fun i _ => mul_pos (hvpos _) (by positivity)) (hvpos _)) (hvpos _)
  have hT : (0 : ℝ) < (2 : ℝ) ^ ((dimN n j : ℝ) / 2) := by positivity
  have hle2 : ENNReal.ofReal c * κ * (ENNReal.ofReal ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) *
      volU (p - ∑ i, j i) * volU (q - ∑ i, j i)) * ENNReal.ofReal ((2 : ℝ) ^ ((dimN n j : ℝ) / 2))) ≤
      ENNReal.ofReal (volU p * volU q) := by
    apply cancel_mul_right_le hB0 hBt
    convert hle using 1
    ring
  have hc0 : 0 ≤ cIw p q j := by
    unfold cIw
    exact (div_pos (mul_pos (by positivity) (mul_pos (hvpos p) (hvpos q))) hAL).le
  have hcIw : ENNReal.ofReal (cIw p q j) * (ENNReal.ofReal ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) *
      volU (p - ∑ i, j i) * volU (q - ∑ i, j i)) * ENNReal.ofReal ((2 : ℝ) ^ ((dimN n j : ℝ) / 2))) =
      ENNReal.ofReal (volU p * volU q) := by
    rw [← ENNReal.ofReal_mul hAL.le, ← ENNReal.ofReal_mul hc0]
    congr 1
    have h2 : (2 : ℝ) ^ (-((dimN n j : ℝ) / 2)) * (2 : ℝ) ^ ((dimN n j : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    unfold cIw
    rw [hpq]
    rw [show ∀ x y z w : ℝ, x * y / z * (z * w) = x * w * y * (z / z) by intros; ring, div_self hAL.ne', h2]
    ring
  have hne0 : ENNReal.ofReal ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) *
      volU (p - ∑ i, j i) * volU (q - ∑ i, j i)) * ENNReal.ofReal ((2 : ℝ) ^ ((dimN n j : ℝ) / 2)) ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hAL).ne' (ENNReal.ofReal_pos.mpr hT).ne'
  have hnet : ENNReal.ofReal ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) *
      volU (p - ∑ i, j i) * volU (q - ∑ i, j i)) * ENNReal.ofReal ((2 : ℝ) ^ ((dimN n j : ℝ) / 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  exact cancel_mul_right_le hne0 hnet (hle2.trans_eq hcIw.symm)

end GlobalTheory.IwConst
