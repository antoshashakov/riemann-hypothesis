import Lib.Analytic.EntireLFunction

/-! Landau's lemma: one-sided exponential bounds and nonnegative real residues exclude poles
to the right of the bound. The compact proof is due to Luke Sernau and collaborators, based on
Alpöge's proof (grh-compact, 72fead102f663d5c7a407964a13dc0cf9d977207). The final exponent bridge
preserves the existing public criterion with an arbitrary real leading constant. -/

open ArithmeticFunction DirichletCharacter Complex Set Filter MeasureTheory Metric ProbabilityTheory
  Nat Topology ComplexOrder AnalyticOnNhd Real
namespace New
variable {E : ℝ → ℝ} {s : ℂ}
attribute [local simp] Complex.norm_exp MeasureTheory.integral_const_mul
  MeasureTheory.integral_mul_const sub_eq_zero

private lemma summable_taylor_of_removable {Ψ ε} {a z : ℂ} σ (D :
  AnalyticOnNhd ℂ (fun z ↦ (z - a) * Ψ z) (ball z ε)) (u : z ≠ a ∧ a ∈ ball z ε ∧ σ ∈ ball z ε) :
  Summable fun k ↦ (k ! : ℂ)⁻¹ • (σ - z) ^ k • iteratedDeriv k Ψ z := (hasSum_taylorSeries_on_ball
  ((differentiableOn_dslope (isOpen_ball.mem_nhds u.2.1)).2 D.differentiableOn) u.2.2
  ).summable.congr (by erw [(eqOn_dslope_sub_smul ..).iteratedDeriv_of_isOpen isOpen_ne · u.1])

theorem IsPolar.compactLandauConstOne {r} (h : IsPolar E r) {β : ℝ} (hβ : 0 < β)
    (hr : ∀ x, β < x → 0 ≤ (r x).re)
    (hw : ∀ᶠ v in atTop, E v ≤ ((β - 1) * v).exp) {ρ} (hρ : β < ρ.re) : r ρ = 0 := by
  obtain ⟨⟨m, C, Φ, M, hC, e, h⟩, Y, hY⟩ := h, eventually_atTop.1 hw
  let K := 1 ⊔ |C| * Y.exp ^ 2
  let μ := (volume.restrict (Ioi 0)).withDensity fun v ↦ (K * (β * v).exp - E v * v.exp).toNNReal
  let S := integrableExpSet (-|·|) μ; let Ψ s := K / (s - β) - Φ s
  have e s (u : 2 < s.re) (w : β - s.re < 0) : s.re ∈ S ∧ complexMGF (-|·|) μ s = Ψ s := by
    obtain ⟨i, j⟩ := (@integrableOn_exp_mul_complex_Ioi (β - s) w 0).const_mul K,
      integrableOn_laplace_of_abs_le m hC u
    refine ⟨((integrable_withDensity_iff_integrable_coe_smul (by fun_prop)).2 ((i.sub j).congr ?q)
      ).norm.congr (by simp), (integral_withDensity_eq_integral_smul (by fun_prop) _).trans (
      integral_congr_ae ?q ▸ by simp [integral_sub i j, integral_exp_mul_complex_Ioi, w]; grind)⟩
    filter_upwards [ae_restrict_mem (by simp)] with v u
    rw [coe_toNNReal, abs_of_pos u]
    simp [sub_mul, mul_assoc, ← Complex.exp_add]; rfl
    cases le_total Y v <;> [grw [hY, sub_mul, Real.exp_sub]; grw [le_of_abs_le (hC ..),
      ← one_le_exp]] <;> simp [field, *, u.out.le] <;> bound
  have H ρ u := ((ContinuousWithinAt.tendsto (by
    have hn : ρ ≠ (β : ℂ) := fun e ↦ (ne_of_gt u) (by simpa using congrArg Complex.re e)
    fun_prop (disch := exact sub_ne_zero.mpr hn))).sub (h ρ
    (hβ.trans u))).congr fun z ↦ (.symm (mul_sub ..) : _ = _ * Ψ z)
  obtain ⟨a, ha⟩ := exists_isLUB (Sᶜ.insert_nonempty β) ⟨2 + β, (by grind [e ⟨·, 0⟩])⟩
  obtain ⟨A, T⟩ := interior_maximal (fun x ↦ (·.not_ge.imp_symm (ha.1 <| .inr ·))) isOpen_Ioi,
    ((hasDerivAt_id' a).ofReal_comp.tendsto_nhdsNE one_ne_zero).mono_left (nhdsGT_le_nhdsNE a)
  obtain ⟨N : Meromorphic Ψ, G⟩ := fun _ ↦ by fun_prop, analyticOnNhd_complexMGF.mono (@A ·.re)
  have I {ρ} hρ := eventuallyEq_iff_sub.2 <| meromorphicOrderAt_eq_top_iff.1 <| ((
   N.meromorphicOn.fun_sub G.meromorphicOn).meromorphicOrderAt_ne_top_of_isPreconnected (x := ρ)
   (convex_halfSpace_re_gt a).isPreconnected hρ (by grind : a < re ⟨a ⊔ β + 3, 0⟩)).mtr <|
   meromorphicOrderAt_eq_top_iff.2 (mem_nhdsWithin.2 ⟨_, isOpen_re_gt (2 + β), by clear hr; grind⟩)
  obtain rfl | p := (ha.1 (.inl rfl)).eq_or_lt
  simpa using tendsto_nhds_unique ((H ρ hρ).congr' (I hρ).mul_left)
    (tendsto_inf_left (.mul (.sub_const le_rfl ρ) (G _ hρ).continuousAt))
  have J := (T.eventually (N a).eventually_analyticAt).mp (mem_inf_of_right
    fun z u B ↦ (B.frequently_eq_iff_eventually_eq (G _ u)).1 (I u).frequently)
  obtain ⟨ε, o, D⟩ := (MeromorphicAt.analyticAt (by fun_prop) (continuousWithinAt_compl_self.1
    ((H a p).trans_eq congr(𝓝 $((ge_of_tendsto ((H a p).comp T) (J.mp (mem_inf_of_right fun z u B ↦
    by simp [B.self_of_nhds, complexMGF_ofReal, mul_nonneg, u.out.le, mgf_nonneg]))).eq_of_not_lt'
    (·.1.not_ge (by simp_all))))))).exists_ball_analyticOnNhd
  obtain ⟨z, J, w, g⟩ := (J.and (Ioo_mem_nhdsGT (by bound : a < ε / 2 + a))).exists
  obtain ⟨⟨σ, n, v⟩, _⟩ := ha.exists_between (max_lt p (sub_left_lt_of_lt_add g)),
    integrable_pow_mul_exp_of_mem_interior_integrableExpSet (A w)
  use n.elim (by order) <| absurd ⟨by fun_prop, (((lintegral_tsum (by fun_prop)).trans (tsum_congr
   fun k ↦ ?_)).trans_lt
    ((summable_taylor_of_removable σ (D.mono (ball_half_subset ↑z ?_)) ?_).mapL reCLM
   ).tsum_ofReal_lt_top).trans_le' <| lintegral_mono fun y ↦ ((NormedSpace.exp_series_hasSum_exp'
   (𝕂 := ℝ) ((σ - z) * -|y|)).mul_right (z * -|y|).exp).tsum_eq.trans ?_ ▸
      enorm_tsum_le_tsum_enorm⟩
  rw [EventuallyEq.iteratedDeriv_eq k J, iteratedDeriv_complexMGF]
  simp_rw [← integral_smul, smul_eq_mul, ← ofReal_natCast, mul_pow, mul_assoc]
  rw_mod_cast [← ofReal_integral_norm_eq_lintegral_enorm (by fun_prop)]
  all_goals simp [← mul_pow, ← mul_assoc, ← neg_mul, dist_eq_norm, ← ofReal_sub,
    ← exp_eq_exp_ℝ, ← Real.exp_add]; clear e H; grind

theorem eventually_const_mul_rpow_le (A β γ : ℝ) (h : β < γ) :
    ∀ᶠ x : ℝ in atTop, A * x ^ (β - 1) ≤ x ^ (γ - 1) := by
  have h_large : ∀ᶠ x : ℝ in atTop, A ≤ x ^ (γ - β) :=
    (tendsto_rpow_atTop (sub_pos.mpr h)).eventually_ge_atTop A
  filter_upwards [h_large, eventually_gt_atTop (0 : ℝ)] with x hx hx_pos
  calc
    A * x ^ (β - 1) ≤ x ^ (γ - β) * x ^ (β - 1) :=
      mul_le_mul_of_nonneg_right hx (rpow_nonneg hx_pos.le _)
    _ = x ^ (γ - 1) := by rw [← rpow_add hx_pos]; congr 1; ring

lemma IsPolar.landau {r : ℂ → ℂ} (h : IsPolar E r) {A β : ℝ} (hβ : 0 < β)
    (hr : ∀ x : ℝ, β < x → 0 ≤ (r x).re) (hE_le : ∀ᶠ v : ℝ in atTop, E v ≤ A * Real.exp ((β - 1) * v))
    {ρ : ℂ} (hρ : β < ρ.re) :
    r ρ = 0  := by
  obtain ⟨γ, hβγ, hγρ⟩ := exists_between hρ
  have hdom : ∀ᶠ v : ℝ in atTop,
      A * Real.exp ((β - 1) * v) ≤ Real.exp ((γ - 1) * v) := by
    have h := tendsto_exp_atTop.eventually (eventually_const_mul_rpow_le A β γ hβγ)
    filter_upwards [h] with v hv
    simpa only [← Real.exp_mul, mul_comm v] using hv
  exact h.compactLandauConstOne (hβ.trans hβγ) (fun x hx ↦ hr x (hβγ.trans hx))
    ((hE_le.and hdom).mono fun _ hv ↦ hv.1.trans hv.2) hγρ

end New
