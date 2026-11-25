module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.RSubPowApply
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.FiniteSystemProof
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ContinuousCompTorusMap
import Mathlib

/-! Jacquet–Langlands torus trace formula `UpperTheory.Esk.TF`: a shorter self-contained proof
(hyperbolic measure, kernel and orbit estimates done directly with Mathlib).
Adapted from Playground attempt #99249 (Osgood001/riemann-hypothesis, Core Pillar 10). -/

@[expose] public section
-- ==== B0

noncomputable section

open MeasureTheory Matrix Set Finset Filter Function Subgroup MulAction QuotientGroup
open Real hiding dist_eq
open _root_.Complex hiding log exp exp_add exp_neg exp_log exp_nat_mul log_mul log_exp exp_sub
open scoped ENNReal NNReal ComplexConjugate Classical Real

namespace UpperTheory.Esk

abbrev oR := ENNReal.ofReal
abbrev a1 := @And.left
abbrev a2 := @And.right
abbrev GL2 (R : Type) [CommRing R] := GL (Fin 2) R

lemma im_smul_jl (g : GL2 ℝ) (z : P) : (g • z).1.im = g.val.det * z.1.im / normSq (den g z.1) :=
    im_div g z.1

lemma nsq_sub_conj (z w : ℂ) : ‖z - conj w‖ ^ 2 = (z.re - w.re) ^ 2 + (z.im + w.im) ^ 2 := by
  rw [Complex.sq_norm, normSq_apply]; simp; ring

lemma pos_den_conj {z w : ℂ} (h : 0 < z.im * w.im) : 0 < ‖z - conj w‖ ^ 2 := by
  rw [nsq_sub_conj]; nlinarith [sq_nonneg (z.re - w.re), sq_nonneg z.im, sq_nonneg w.im]

lemma sub_conj_ne {z w : ℂ} (h : 0 < z.im * w.im) : z - conj w ≠ 0 :=
  norm_ne_zero_iff.1 (sq_pos_iff.1 (pos_den_conj h))

lemma e01_ne {F : Type} [Field F] : (![0,
                                       1] : Fin 2 → F) ≠ 0 := fun h => by simpa using congrFun h 1

lemma rep_spec_jl {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (ω : D.Om) :
    ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := Quotient.out_eq ω

lemma sq_rpow_half {n : ℝ} (hn : 0 ≤ n) (k : ℕ) : (n ^ 2) ^ ((k : ℝ) / 2) = n ^ k := by
  rw [← rpow_natCast n 2, ← rpow_mul hn, ← rpow_natCast n k]; congr 1; push_cast; ring

-- === B1a: Half-plane measure invariance ===

lemma isOpen_U_jl : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne_fun continuous_im continuous_const
lemma openEmb_P : Topology.IsOpenEmbedding (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) :=
    isOpen_U_jl.isOpenEmbedding_subtypeVal
lemma measEmb_P : MeasurableEmbedding (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) :=
    openEmb_P.measurableEmbedding

lemma cont_smul_P (g : GL2 ℝ) : Continuous (fun z : P => g • z) :=
  continuous_induced_rng.2 $ Continuous.div (by unfold num; fun_prop) (by unfold den; fun_prop) fun z => den_ne g z.2

lemma mp_smul_P (g : GL2 ℝ) : MeasurePreserving (fun z : P => g • z) volume volume := by
  let F (h : GL2 ℝ) (z : ℂ) := num h z / den h z
  have hvol (s : Set {z : ℂ // z.im ≠ 0}) (hs : MeasurableSet s) :
      (volume : Measure P) s = ∫⁻ z in Subtype.val '' s, oR (1 / z.im ^ 2) := by
    change (Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume).withDensity (fun z => oR (1 / z.1.im ^ 2)) s = _
    rw [withDensity_apply _ hs, measEmb_P.restrict_comap,
        ← measEmb_P.lintegral_map (f := fun z : ℂ => oR (1 / z.im ^ 2)),
      measEmb_P.map_comap, Measure.restrict_restrict measEmb_P.measurableSet_range, inter_eq_right.2 (image_subset_range _ _)]
  have hkey (h : GL2 ℝ) {S : Set ℂ} (hS : MeasurableSet S) (hSU : S ⊆ {z : ℂ | z.im ≠ 0}) :
      ∫⁻ x in F h '' S, oR (1 / x.im ^ 2) = ∫⁻ x in S, oR (1 / x.im ^ 2) := by
    let D z :=
        (ContinuousLinearMap.toSpanSingleton ℂ ((h.val.det : ℂ) / den h z ^ 2)).restrictScalars ℝ
    have hfd x (hx : x ∈ S) : HasFDerivAt (F h) (D x) x := by
      have hd : HasDerivAt (F h) ((h.val.det : ℂ) / den h x ^ 2) x :=
        ((((hasDerivAt_id x).const_mul ((h 0 0 : ℝ) : ℂ)).add_const _).div
          (((hasDerivAt_id x).const_mul ((h 1 0 : ℝ) : ℂ)).add_const _) (den_ne h (hSU hx))).congr_deriv $ by
            simp only [den, id, mul_one]; rw [det_eq]; push_cast; ring
      simpa [D] using hd.hasFDerivAt.restrictScalars ℝ
    have hinj : InjOn (F h) S := fun x hx y hy hxy => by
      let px : P := ⟨x, hSU hx⟩; let py : P := ⟨y, hSU hy⟩
      exact congrArg Subtype.val (@smul_left_cancel (GL2 ℝ) P _ _ h px py (Subtype.ext hxy))
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS (fun x hx => (hfd x hx).hasFDerivWithinAt) hinj]
    refine setLIntegral_congr_fun hS fun x hx => ?_
    have hd := den_ne h (hSU hx)
    have hn : normSq (den h x) ≠ 0 := by simpa using hd
    have hdet := h.det_ne_zero
    have hdetD : (D x).det = normSq ((h.val.det : ℂ) / den h x ^ 2) := by
      simp [D, ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
    rw [hdetD, abs_of_nonneg (normSq_nonneg _), ← ENNReal.ofReal_mul (normSq_nonneg _)]
    congr 1; rw [im_div, normSq_div, normSq_ofReal, map_pow]; field_simp
  refine ⟨(cont_smul_P g).measurable, Measure.ext fun s hs => ?_⟩
  let s1 : Set {z : ℂ // z.im ≠ 0} := (fun z : P => g • z) ⁻¹' s
  let s2 : Set {z : ℂ // z.im ≠ 0} := s
  rw [Measure.map_apply (cont_smul_P g).measurable hs]
  change (volume : Measure P) s1 = (volume : Measure P) s2
  rw [hvol s1 ((cont_smul_P g).measurable hs), hvol s2 hs]
  have himg : Subtype.val '' s1 = F g⁻¹ '' (Subtype.val '' s2) := by
    ext x; simp only [Set.mem_image]
    refine ⟨fun ⟨p, hp, hpx⟩ => let p' : P := p; ⟨(g • p').1, ⟨g • p', hp, rfl⟩,
        by change (g⁻¹ • (g • p')).1 = x; rwa [inv_smul_smul]⟩,
      fun ⟨_, ⟨q, hq, rfl⟩, hqx⟩ => let q' : P := q; ⟨g⁻¹ • q',
                                                      by change g • (g⁻¹ • q') ∈ s; rwa [smul_inv_smul], hqx⟩⟩
  rw [himg, hkey g⁻¹ (measEmb_P.measurableSet_image.2 hs) fun _ ⟨p, _, hp⟩ => hp ▸ p.2]

theorem half_plane_measure_invariant_proof_jl : B1a := by
  have hsf : SigmaFinite (Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume) :=
    SigmaFinite.of_map _ measEmb_P.measurable.aemeasurable (by rw [measEmb_P.map_comap]; infer_instance)
  have hm : Measurable (fun z : {z : ℂ // z.im ≠ 0} => oR (1 / z.1.im ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.div ((measurable_im.comp measEmb_P.measurable).pow_const 2))
  refine ⟨@SigmaFinite.withDensity_ofReal _ _ _ hsf _, ⟨fun A hA hne => ?_⟩,
          fun g => ⟨cont_smul_P g, mp_smul_P g⟩⟩
  have : (Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume).IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap _ openEmb_P
  let A' : Set {z : ℂ // z.im ≠ 0} := A
  have hA' : IsOpen A' := hA
  change (Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume).withDensity (fun z => oR (1 / z.1.im ^ 2)) A' ≠ 0
  rw [Ne, withDensity_apply_eq_zero hm,
      show {x : {z : ℂ // z.im ≠ 0} | oR (1 / x.1.im ^ 2) ≠ 0} ∩ A' = A' from
    inter_eq_right.2 fun x _ => by have := x.2; simp [oR]; positivity]
  exact hA'.measure_ne_zero _ hne

-- === B1b & B1c: Automorphy factor, kernel algebra, and kappa properties ===

lemma clopen_pos_im : IsClopen {p : P × P | 0 < p.1.1.im * p.2.1.im} := by
  have hc : Continuous fun p : P × P => p.1.1.im * p.2.1.im := by fun_prop
  refine ⟨?_, isOpen_lt continuous_const hc⟩
  rw [show {p : P × P | 0 < p.1.1.im * p.2.1.im} = {p : P × P | 0 ≤ p.1.1.im * p.2.1.im} from
    Set.ext fun p => by simp only [Set.mem_ofPred_eq]; exact ⟨le_of_lt,
                                                              fun h => lt_of_le_of_ne h (mul_ne_zero p.1.2 p.2.2).symm⟩]
  exact isClosed_le continuous_const hc

lemma den_mul_jl (g h : GL2 ℝ) (z : P) : den (g * h) z.1 = den g (h • z).1 * den h z.1 := by
  have h0 := den_ne h z.2; rw [coe_smul]
  conv_rhs => rw [den, add_mul, mul_assoc, div_mul_cancel₀ _ h0]
  simp [num, den, Matrix.mul_apply, Fin.sum_univ_two]; ring

lemma j1_mul (k : ℕ) (g h : GL2 ℝ) (z : P) : j1 k (g * h) z = j1 k g (h • z) * j1 k h z := by
  simp only [j1, den_mul_jl, mul_pow, Units.val_mul, Matrix.det_mul, abs_mul,
    mul_rpow (abs_nonneg _) (abs_nonneg _), ofReal_mul]; ring

lemma j1_ne (k : ℕ) (g : GL2 ℝ) (z : P) : j1 k g z ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (den_ne g z.2)) (ofReal_ne_zero.2 (rpow_pos_of_pos (abs_pos.2 g.det_ne_zero) _).ne')

lemma sub_conj_smul (g : GL2 ℝ) (z w : P) :
    (g • z).1 - conj (g • w).1 = (g.val.det : ℂ) * (z.1 - conj w.1) / (den g z.1 * conj (den g w.1)) := by
  rw [coe_smul, coe_smul, map_div₀,
      div_sub_div _ _ (den_ne g z.2) ((map_ne_zero _).2 (den_ne g w.2))]
  congr 1; simp only [num, den, map_add, map_mul, conj_ofReal, det_eq]; push_cast; ring

lemma sign_smul (g : GL2 ℝ) (z w : P) : 0 < (g • z).1.im * (g • w).1.im ↔ 0 < z.1.im * w.1.im := by
  rw [im_smul_jl, im_smul_jl]
  have hd := g.det_ne_zero
  have nz : 0 < normSq (den g z.1) := normSq_pos.2 (den_ne g z.2)
  have nw : 0 < normSq (den g w.1) := normSq_pos.2 (den_ne g w.2)
  have hc : 0 < g.val.det ^ 2 / (normSq (den g z.1) * normSq (den g w.1)) := by positivity
  rw [show g.val.det * z.1.im / normSq (den g z.1) * (g.val.det * w.1.im / normSq (den g w.1))
      = g.val.det ^ 2 / (normSq (den g z.1) * normSq (den g w.1)) * (z.1.im * w.1.im) by field_simp]
  exact mul_pos_iff_of_pos_left hc

lemma q1_smul (k : ℕ) (g : GL2 ℝ) (z w : P) : q1 k (g • z) (g • w) * j1 k g w = j1 k g z * q1 k z w := by
  unfold q1; rw [if_congr (sign_smul g z w) rfl rfl]
  split_ifs with h
  · have hd : (g.val.det : ℂ) ≠ 0 := ofReal_ne_zero.2 g.det_ne_zero
    have h1 := den_ne g z.2; have h2 := den_ne g w.2
    have h3 : conj (den g w.1) ≠ 0 := (map_ne_zero _).2 h2
    have h4 := sub_conj_ne h
    have hrat : ((g • w).1 - conj (g • w).1) / ((g • z).1 - conj (g • w).1)
        = (w.1 - conj w.1) / (z.1 - conj w.1) * (den g z.1 / den g w.1) := by
      rw [sub_conj_smul, sub_conj_smul]; field_simp
    rw [hrat, mul_pow, div_pow, div_pow]; have := pow_ne_zero k h2; simp only [j1]; field_simp
  · simp

lemma kap_smul_jl (g : GL2 ℝ) (z w : P) : kap (g • z) (g • w) = kap z w := by
  unfold kap; rw [if_congr (sign_smul g z w) rfl rfl]
  split_ifs with h
  · have hd := g.det_ne_zero
    have nz : normSq (den g z.1) ≠ 0 := (normSq_pos.2 (den_ne g z.2)).ne'
    have nw : normSq (den g w.1) ≠ 0 := (normSq_pos.2 (den_ne g w.2)).ne'
    have h4 : ‖z.1 - conj w.1‖ ≠ 0 := norm_ne_zero_iff.2 (sub_conj_ne h)
    rw [im_smul_jl, im_smul_jl, sub_conj_smul, norm_div, norm_mul, norm_mul, norm_conj, norm_real,
      Real.norm_eq_abs, div_pow, mul_pow, mul_pow, sq_abs]
    simp only [Complex.sq_norm]; field_simp
  · rfl

lemma norm_j1 (k : ℕ) (g : GL2 ℝ) (z : P) : ‖j1 k g z‖ * |(g • z).1.im| ^ ((k : ℝ) / 2) = |z.1.im| ^ ((k : ℝ) / 2) := by
  have hD : 0 < ‖den g z.1‖ := norm_pos_iff.2 (den_ne g z.2)
  have hdet : 0 < |g.val.det| := abs_pos.2 g.det_ne_zero
  rw [j1, im_smul_jl, normSq_eq_norm_sq, abs_div, abs_mul, abs_of_nonneg (sq_nonneg ‖den g z.1‖),
    norm_mul, norm_pow, norm_real, Real.norm_of_nonneg (rpow_nonneg (abs_nonneg _) _),
    div_rpow (by positivity) (by positivity), mul_rpow (abs_nonneg _) (abs_nonneg _), sq_rpow_half (norm_nonneg _)]
  have hinv : |g.val.det| ^ (-(k : ℝ) / 2) * |g.val.det| ^ ((k : ℝ) / 2) = 1 := by
    rw [neg_div, rpow_neg (abs_nonneg _), inv_mul_cancel₀ (rpow_pos_of_pos hdet _).ne']
  have hDk : ‖den g z.1‖ ^ k ≠ 0 := pow_ne_zero _ hD.ne'
  calc ‖den g z.1‖ ^ k * |g.val.det| ^ (-(k : ℝ) / 2) * (|g.val.det| ^ ((k : ℝ) / 2) * |z.1.im| ^ ((k : ℝ) / 2) / ‖den g z.1‖ ^ k)
      = (|g.val.det| ^ (-(k : ℝ) / 2) * |g.val.det| ^ ((k : ℝ) / 2)) * |z.1.im| ^ ((k : ℝ) / 2) * (‖den g z.1‖ ^ k / ‖den g z.1‖ ^ k) :=
          by ring
    _ = _ := by rw [hinv, div_self hDk, one_mul, mul_one]

lemma norm_q1 (k : ℕ) (z w : P) (hk : 1 ≤ k) :
    ‖q1 k z w‖ * |z.1.im| ^ ((k : ℝ) / 2) = ((k : ℝ) - 1) / (4 * π) * kap z w ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold q1 kap; split_ifs with h
  · have hdn : 0 < ‖z.1 - conj w.1‖ := norm_pos_iff.2 (sub_conj_ne h)
    have hww : ‖w.1 - conj w.1‖ = 2 * |w.1.im| := by
      rw [Complex.sub_conj, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_mul,
          abs_two]
    have hc : ‖((k : ℂ) - 1) / (4 * π)‖ = ((k : ℝ) - 1) / (4 * π) := by
      rw [show ((k : ℂ) - 1) / (4 * π) = (((k : ℝ) - 1) / (4 * π) : ℝ) by push_cast; ring,
        norm_real, Real.norm_of_nonneg (div_nonneg (by linarith) (by positivity))]
    have hzw : z.1.im * w.1.im = |z.1.im| * |w.1.im| := by rw [← abs_mul, abs_of_pos h]
    have h4 : (4 : ℝ) ^ ((k : ℝ) / 2) = 2 ^ k := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
                                                        sq_rpow_half (by norm_num)]
    have hsq : |w.1.im| ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2) = |w.1.im| ^ k := by
      rw [← mul_rpow (abs_nonneg _) (abs_nonneg _), ← sq, sq_rpow_half (abs_nonneg _)]
    rw [norm_mul, hc, norm_pow, norm_div, hww, hzw, div_rpow (by positivity) (by positivity),
      sq_rpow_half hdn.le, mul_rpow (by norm_num) (by positivity), mul_rpow (abs_nonneg _) (abs_nonneg _),
      h4, div_pow, mul_pow, ← hsq]; ring
  · rw [norm_zero, zero_mul, zero_rpow (by linarith), mul_zero, zero_mul]

lemma cont_j1 (k : ℕ) (g : GL2 ℝ) : Continuous (j1 k g) := by unfold j1 den; fun_prop

lemma cont_q1 (k : ℕ) : Continuous fun p : P × P => q1 k p.1 p.2 := by
  unfold q1
  refine continuous_if (fun a ha => (clopen_pos_im.frontier_eq ▸ ha).elim) ?_ continuousOn_const
  rw [clopen_pos_im.1.closure_eq]
  exact (continuousOn_const.mul ((Continuous.continuousOn (by fun_prop)).div
    (Continuous.continuousOn (by fun_prop)) (fun p hp => sub_conj_ne hp) |>.pow k))

lemma hol_q1 (k : ℕ) (w : P) : Hol1 fun z => q1 k z w := fun t ht => by
  apply DifferentiableAt.differentiableWithinAt
  have hcont : Continuous fun s : ℂ => s.im * w.1.im := continuous_im.mul continuous_const
  by_cases hp : 0 < t.im * w.1.im
  · refine (show DifferentiableAt ℂ (fun s => ((k : ℂ) - 1) / (4 * π) * ((w.1 - conj w.1) / (s - conj w.1)) ^ k) t by
      fun_prop (disch := exact sub_conj_ne hp)).congr_of_eventuallyEq ?_
    filter_upwards [(hcont.tendsto t).eventually (lt_mem_nhds hp)] with s hs
    have hs' : s.im ≠ 0 := fun h0 => by simp [h0] at hs
    simp [ext1, hs', q1, hs]
  · have hneg : t.im * w.1.im < 0 := lt_of_le_of_ne (not_lt.1 hp) (mul_ne_zero ht w.2)
    refine (differentiableAt_const 0).congr_of_eventuallyEq ?_
    filter_upwards [(hcont.tendsto t).eventually (gt_mem_nhds hneg)] with s hs
    by_cases hs' : s.im ≠ 0 <;> simp [ext1, hs', q1, not_lt.2 hs.le]

theorem automorphy_factor_kernel_algebra_proof_jl : B1b :=
  ⟨j1_mul, j1_ne, q1_smul, kap_smul_jl, norm_j1, norm_q1, cont_j1, cont_q1, hol_q1⟩

lemma kap_nonneg_jl (z w : P) : 0 ≤ kap z w := by
  unfold kap; split_ifs with h; exact div_nonneg (by linarith) (sq_nonneg _); exact le_rfl

lemma kap_le_one (z w : P) : kap z w ≤ 1 := by
  unfold kap; split_ifs with h
  · rw [div_le_iff₀ (pos_den_conj h), nsq_sub_conj]
    nlinarith [sq_nonneg (z.1.re - w.1.re), sq_nonneg (z.1.im - w.1.im)]
  · norm_num

lemma kap_symm (z w : P) : kap z w = kap w z := by
  unfold kap; rw [mul_comm z.1.im w.1.im,
                  show ‖z.1 - conj w.1‖ ^ 2 = ‖w.1 - conj z.1‖ ^ 2 by rw [nsq_sub_conj,
                                                                          nsq_sub_conj]; ring]

lemma kap_self (z : P) : kap z z = 1 := by
  have h := mul_self_pos.2 z.2
  rw [kap, ite_eq_left h, div_eq_one_iff_eq (pos_den_conj h).ne', nsq_sub_conj]; ring

lemma kap_tri (z w u : P) : kap z w * kap w u ≤ 4 * kap z u := by
  unfold kap; split_ifs with h1 h2 h13
  · have hkey : w.1.im ^ 2 * ‖z.1 - conj u.1‖ ^ 2 ≤ ‖z.1 - conj w.1‖ ^ 2 * ‖w.1 - conj u.1‖ ^ 2 := by
      have hp : 0 ≤ z.1.im ^ 2 + 2 * z.1.im * w.1.im := by nlinarith [sq_nonneg z.1.im]
      have hq : 0 ≤ u.1.im ^ 2 + 2 * w.1.im * u.1.im := by nlinarith [sq_nonneg u.1.im]
      rw [nsq_sub_conj, nsq_sub_conj, nsq_sub_conj]
      nlinarith [sq_nonneg ((z.1.re - w.1.re) * (w.1.re - u.1.re) - w.1.im ^ 2),
        mul_nonneg (sq_nonneg (z.1.re - w.1.re)) hq, mul_nonneg (sq_nonneg (w.1.re - u.1.re)) hp,
        mul_nonneg (sq_nonneg w.1.im) h1.le, mul_nonneg (sq_nonneg w.1.im) h2.le,
        mul_nonneg (sq_nonneg w.1.im) h13.le, mul_nonneg h13.le h1.le, mul_nonneg h13.le h2.le,
        sq_nonneg (z.1.im * u.1.im)]
    rw [div_mul_div_comm, mul_div_assoc', le_div_iff₀ (pos_den_conj h13), div_mul_eq_mul_div,
      div_le_iff₀ (mul_pos (pos_den_conj h1) (pos_den_conj h2))]
    nlinarith [mul_le_mul_of_nonneg_left hkey h13.le]
  · exfalso; have hc := not_lt.1 h13
    nlinarith [mul_pos h1 h2, mul_nonneg (neg_nonneg.2 hc) (sq_nonneg w.1.im)]
  all_goals simp; try positivity

lemma kap_im_le (z w : P) : kap z w * |w.1.im| ≤ 4 * |z.1.im| := by
  unfold kap; split_ifs with h
  · rw [div_mul_eq_mul_div, div_le_iff₀ (pos_den_conj h), nsq_sub_conj]
    rcases lt_or_gt_of_ne w.2 with hw | hw
    · have hz : z.1.im < 0 := by nlinarith
      rw [abs_of_neg hw, abs_of_neg hz]
      nlinarith [mul_nonneg (neg_nonneg.2 hz.le) (sq_nonneg (z.1.re - w.1.re)),
        mul_nonneg (neg_nonneg.2 hz.le) (sq_nonneg z.1.im), mul_nonneg (sq_nonneg z.1.im) (neg_nonneg.2 hw.le)]
    · have hz : 0 < z.1.im := by nlinarith
      rw [abs_of_pos hw, abs_of_pos hz]
      nlinarith [mul_nonneg hz.le (sq_nonneg (z.1.re - w.1.re)),
        mul_nonneg hz.le (sq_nonneg z.1.im), mul_nonneg (sq_nonneg z.1.im) hw.le]
  · rw [zero_mul]; positivity

lemma cont_kap : Continuous fun p : P × P => kap p.1 p.2 := by
  show Continuous fun p : P × P => if 0 < p.1.1.im * p.2.1.im then
    4 * (p.1.1.im * p.2.1.im) / ‖p.1.1 - conj p.2.1‖ ^ 2 else 0
  refine continuous_if (fun a ha => (clopen_pos_im.frontier_eq ▸ ha).elim) ?_ continuousOn_const
  rw [clopen_pos_im.1.closure_eq]
  have hn : Continuous fun p : P × P => 4 * (p.1.1.im * p.2.1.im) := by fun_prop
  have hd : Continuous fun p : P × P => ‖p.1.1 - conj p.2.1‖ ^ 2 := by fun_prop
  exact hn.continuousOn.div hd.continuousOn fun p hp => (pos_den_conj hp).ne'

lemma trans_iP (z : P) : ∃ g : GL2 ℝ, g 1 0 = 0 ∧ g 1 1 = 1 ∧ g • iP = z := by
  have hd : (!![z.1.im, z.1.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [det_fin_two_of]; simpa using z.2
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hd, rfl, rfl, Subtype.ext ?_⟩
  change num (GeneralLinearGroup.mkOfDetNeZero _ hd) I / den (GeneralLinearGroup.mkOfDetNeZero _ hd) I = z.1
  apply Complex.ext <;> simp [num, den]

theorem hyperbolic_kappa_properties_proof_jl : B1c :=
  ⟨fun z w => ⟨kap_nonneg_jl z w, kap_le_one z w, kap_symm z w⟩, kap_self, kap_tri, kap_im_le,
   cont_kap, trans_iP⟩

-- === E0a: Actions preserve measures & small-ball volume lower bound ===

lemma count_pres_jl {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] (f : α → α)
    (hf : Bijective f) : MeasurePreserving f Measure.count Measure.count := by
  refine ⟨measurable_of_countable f, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_of_countable f) hs, Measure.count_apply hs,
    Measure.count_apply (to_countable _).measurableSet]
  exact congrArg _ $ encard_preimage_of_injective_subset_range hf.1 (hf.2.range_eq ▸ subset_univ s)

theorem actions_preserve_measures_proof_jl : B1a → B1b → B1c → E0a := by
  intro _ _ _ F I Gf _ _ _ D ax
  have : SigmaFinite (volume : Measure P) := half_plane_measure_invariant_proof_jl.1
  have : (volume : Measure P).IsOpenPosMeasure := half_plane_measure_invariant_proof_jl.2.1
  have : Countable F := ax.cF
  have hPG : Countable (PG F) :=
    letI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
    letI : Countable (GL2 F) :=
        Injective.countable (f := fun g : GL2 F => (g : Matrix (Fin 2) (Fin 2) F)) fun _ _ h => Units.ext h
    QuotientGroup.mk_surjective.countable
  have : Countable D.Om := ax.cO; have : Countable D.Cj := hPG
  have : SigmaFinite (volume : Measure D.Xs) :=
      inferInstanceAs (SigmaFinite (Measure.pi fun _ : I => (volume : Measure P)))
  have presX (γ : PG F) : MeasurePreserving (fun z : D.Xs => γ • z) volume volume := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    exact measurePreserving_pi _ _ fun v => mp_smul_P (D.r v g)
  have contX (γ : PG F) : Continuous fun z : D.Xs => γ • z := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    exact continuous_pi fun v => (cont_smul_P (D.r v g)).comp (continuous_apply v)
  refine ⟨hPG, this, presX,
    fun γ => (count_pres_jl (γ • ·) (MulAction.bijective γ)).prod (presX γ),
    fun γ => (count_pres_jl (γ • ·) (MulAction.bijective γ)).prod (presX γ),
    contX, inferInstanceAs (BorelSpace (I → P)), fun δ hδ => ?_⟩
  have hk1 (z : P) : Continuous (kap z) := cont_kap.comp (continuous_const.prodMk continuous_id)
  have hUp : 0 < volume {w : P | δ < kap iP w} :=
    (isOpen_lt continuous_const (hk1 iP)).measure_pos volume ⟨iP, by simpa [kap_self] using hδ⟩
  obtain ⟨c0, hc0, hc0U⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hUp
  have hS (z : P) : MeasurableSet {w | δ ≤ kap z w} :=
      measurableSet_le measurable_const (hk1 z).measurable
  have hball (z : P) : (c0 : ℝ≥0∞) ≤ volume {w | δ ≤ kap z w} := by
    obtain ⟨g, -, -, rfl⟩ := trans_iP z
    rw [← (mp_smul_P g).measure_preimage (hS _).nullMeasurableSet,
      show (g • ·) ⁻¹' {w | δ ≤ kap (g • iP) w} = {w | δ ≤ kap iP w} from Set.ext fun w => by simp [kap_smul_jl]]
    exact hc0U.le.trans $ measure_mono fun _ (h : δ < kap iP _) => show δ ≤ kap iP _ from h.le
  refine ⟨c0 ^ Fintype.card I, pow_pos (by exact_mod_cast hc0) _, fun z => ?_⟩
  rw [show {w : X I | Near δ z w} = univ.pi fun v => {w | δ ≤ kap (z v) w} from Set.ext fun w => by simp [Near]]
  refine ⟨MeasurableSet.univ_pi fun v => hS (z v), ?_⟩
  rw [volume_pi, Measure.pi_pi, ENNReal.coe_pow, ← card_univ, ← prod_const]
  exact Finset.prod_le_prod fun v _ => hball (z v)

-- === Pack & Mult ===

lemma kap_smulX {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (δ : PG F) (a b : D.Xs) (v : I) :
    kap ((δ • a : D.Xs) v) ((δ • b : D.Xs) v) = kap (a v) (b v) := by
  induction δ using QuotientGroup.induction_on with
  | H g => exact kap_smul_jl (D.r v g) (a v) (b v)

theorem pf_Pack_jl : B1b → B1c → E0a → Pack := by
  intro _ _ hE F I Gf _ _ _ D hax
  obtain ⟨hcnt, -, -, -, -, -, -, hnear⟩ := hE F I Gf D hax
  obtain ⟨c, hc0, hcz⟩ := hnear (1 / 2) (by norm_num)
  refine ⟨c⁻¹, fun y ω' h A hh hA hfin => ?_⟩
  set S0 : Set (PG F) := {γ | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)}
  set N : ℝ≥0∞ := (S0.ncard : ℝ≥0∞)
  let Γ := {γ : PG F // γ • y.1 = ω'}
  let Sg (γ : Γ) : Set D.Xs := {w | Near (1 / 2) (γ.1 • y.2 : D.Xs) w}
  have hSm (γ : Γ) : MeasurableSet (Sg γ) := (hcz (γ.1 • y.2)).1
  have hone (γ : Γ) : (c : ℝ≥0∞) * h (γ.1 • y.2) ≤ A * ∫⁻ w, (Sg γ).indicator h w := by
    calc (c : ℝ≥0∞) * h (γ.1 • y.2) ≤ h (γ.1 • y.2) * volume (Sg γ) :=
        by rw [mul_comm]; gcongr; exact (hcz _).2
      _ = ∫⁻ _ in Sg γ, h (γ.1 • y.2) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ w in Sg γ, (A : ℝ≥0∞) * h w := setLIntegral_mono' (hSm γ) fun w hw => hA _ _ hw
      _ = A * ∫⁻ w, (Sg γ).indicator h w := by rw [lintegral_const_mul _ hh,
                                                   lintegral_indicator (hSm γ)]
  have hcnt_w (w : D.Xs) : ∑' γ : Γ, (Sg γ).indicator h w ≤ N * h w := by
    by_cases hT : ∃ γ₁ : Γ, w ∈ Sg γ₁
    · obtain ⟨γ₁, hγ₁⟩ := hT
      have finj : Injective (fun γ : Γ => γ₁.1⁻¹ * γ.1) :=
          fun _ _ h => Subtype.ext (mul_left_cancel h)
      refine (ENNReal.tsum_le_tsum fun γ => ?_).trans ((ENNReal.tsum_comp_le_tsum_of_injective finj (S0.indicator fun _ => h w)).trans ?_)
      · by_cases hw : w ∈ Sg γ
        · have hmem : γ₁.1⁻¹ * γ.1 ∈ S0 := ⟨by rw [mul_smul, γ.2, inv_smul_eq_iff]; exact γ₁.2.symm,
                                            fun v => by
            have e : kap (y.2 v) (((γ₁.1⁻¹ * γ.1) • y.2 : D.Xs) v) = kap ((γ₁.1 • y.2 : D.Xs) v) ((γ.1 • y.2 : D.Xs) v) := by
              rw [← kap_smulX D γ₁.1 y.2 ((γ₁.1⁻¹ * γ.1) • y.2) v, smul_smul, mul_inv_cancel_left]
            rw [e]; have := kap_tri ((γ₁.1 • y.2 : D.Xs) v) (w v) ((γ.1 • y.2 : D.Xs) v)
            rw [kap_symm (w v)] at this; nlinarith [hγ₁ v, hw v]⟩
          simp [indicator_of_mem hw, indicator_of_mem hmem]
        · rw [indicator_of_notMem hw]; exact bot_le
      · rw [← tsum_subtype S0 fun _ => h w]
        have := hfin.fintype
        rw [tsum_fintype, sum_const, card_univ, nsmul_eq_mul,
            ← Nat.card_eq_fintype_card]; simp only [N, Set.ncard_def]; exact le_rfl
    · simp only [not_exists] at hT; have h0 : ∀ γ, (Sg γ).indicator h w = 0 :=
        fun γ => indicator_of_notMem (hT γ) h; simp [h0]
  have hkey : (c : ℝ≥0∞) * ∑' γ : Γ, h (γ.1 • y.2) ≤ A * (N * ∫⁻ w, h w) := by
    rw [← ENNReal.tsum_mul_left]
    calc _ ≤ ∑' γ, (A : ℝ≥0∞) * ∫⁻ w, (Sg γ).indicator h w := ENNReal.tsum_le_tsum hone
      _ = A * ∫⁻ w, ∑' γ, (Sg γ).indicator h w := by rw [ENNReal.tsum_mul_left,
                                                         lintegral_tsum fun γ => (hh.indicator (hSm γ)).aemeasurable]
      _ ≤ A * (N * ∫⁻ w, h w) := by rw [← lintegral_const_mul _ hh]; gcongr; exact hcnt_w _
  have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0.ne'
  calc ∑' γ : Γ, h (γ.1 • y.2) = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * ∑' γ : Γ, h (γ.1 • y.2)) :=
        (ENNReal.inv_mul_cancel_left hc' ENNReal.coe_ne_top).symm
    _ ≤ (c : ℝ≥0∞)⁻¹ * (A * (N * ∫⁻ w, h w)) := by gcongr
    _ = ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * A * N * ∫⁻ w, h w := by rw [ENNReal.coe_inv hc0.ne']; ring

theorem pf_Mult_jl : B1b → E0d → Mult := by
  intro _ hE F I Gf _ _ _ D hD δ c₀ hδ hc₀
  obtain ⟨-, h2, h3, -, -, -, -, -, -, h10, -⟩ := hE F I Gf D hD
  obtain ⟨S, C, c, hc, hnorm⟩ := hD.normal c₀ hc₀
  let A (y : D.Y) : Set (PG F) := {γ | γ • y.1 = y.1 ∧ Near δ y.2 (γ • y.2 : D.Xs)}
  have hconj (g : PG F) (y : D.Y) : (A (g • y)).Finite ↔ (A y).Finite ∧ (A (g • y)).ncard = (A y).ncard := by
    have hinj : Injective (fun γ : PG F => g * γ * g⁻¹) := fun _ _ h => by simpa using h
    have hmem (γ : PG F) : g * γ * g⁻¹ ∈ A (g • y) ↔ γ ∈ A y := by
      simp [A, Near, mul_smul, inv_smul_smul, kap_smulX]
    have hA : A (g • y) = (fun γ => g * γ * g⁻¹) '' A y := Set.ext fun γ' =>
      ⟨fun h => ⟨g⁻¹ * γ' * g, (hmem _).1 (by rwa [show g * (g⁻¹ * γ' * g) * g⁻¹ = γ' by group]),
                 by group⟩,
       fun ⟨γ, hγ, h⟩ => h ▸ (hmem γ).2 hγ⟩
    rw [hA, finite_image_iff hinj.injOn, ncard_image_of_injective _ hinj]
    exact ⟨fun h => ⟨h, rfl⟩, a1⟩
  choose C' hC' using fun x' : Gf => hD.count (x' : Gf ⧸ D.H) δ C c hδ hc
  have hapos x : 0 < D.hf ![0, 1] (D.rep (x : Gf ⧸ D.H)) := hD.pos _ e01_ne _
  refine ⟨∑ x ∈ S, max (C' x) 0 * (1 + 1 / D.hf ![0, 1] (D.rep (x : Gf ⧸ D.H))),
          fun y s hs hy => ?_⟩
  obtain ⟨γ₀, hγ₀⟩ := h10 s hs
  have e1 : D.HtY ![0, 1] ((γ₀ : PG F) • y) = D.HtY s y := by rw [h2 _ e01_ne γ₀ y, hγ₀]
  obtain ⟨b, hb10, ⟨x', hx'S, h, hh, hbx⟩, hsg⟩ := hnorm _ _ (e1.symm ▸ hy)
  have hb11 : b.val 1 1 ≠ 0 := fun h0 => b.det_ne_zero $ by rw [det_fin_two]; simp [h0, hb10]
  have hvb : ![0, 1] ᵥ* b.val = b.val 1 1 • ![(0 : F),
                                              1] := funext fun i => by fin_cases i <;> simp [vecMul,
                                                                                             dotProduct, Fin.sum_univ_two, hb10]
  have hy'' : (b : PG F) • ((γ₀ : PG F) • y) = ((((x' : Gf ⧸ D.H) : D.Om),
                                                 D.act b ((γ₀ : PG F) • y).2) : D.Y) := by
    refine Prod.ext ?_ (D.mk_smulX b _)
    change (b : PG F) • ((γ₀ : PG F) • y).1 = ((x' : Gf ⧸ D.H) : D.Om)
    have : (b : PG F) • ((γ₀ : PG F) • y).1 = ((D.j b * D.rep ((γ₀ : PG F) • y).1 : Gf) : Gf ⧸ D.H) := by
      conv_lhs => rw [← QuotientGroup.out_eq' ((γ₀ : PG F) • y).1]
      exact D.mk_smulO b _
    rw [this, hbx]; exact QuotientGroup.eq.2 (by simpa using hh)
  have ⟨hfin, hle⟩ := hC' x' _ hsg
  have hfin1 := ((hconj (b : PG F) ((γ₀ : PG F) • y)).1 (hy'' ▸ hfin))
  have hfin0 := ((hconj (γ₀ : PG F) y).1 hfin1.1)
  refine ⟨hfin0.1, ?_⟩
  have hHt : (∏ v, |((D.act b ((γ₀ : PG F) • y).2) v).1.im|) * D.hf ![0,
                                                                      1] (D.rep (x' : Gf ⧸ D.H)) = D.HtY s y := by
    have h1 : D.HtY ![0, 1] ((((x' : Gf ⧸ D.H) : D.Om), D.act b ((γ₀ : PG F) • y).2) : D.Y) =
        (∏ v, |((D.act b ((γ₀ : PG F) • y).2) v).1.im|) * D.hf ![0,
                                                                 1] (D.rep (x' : Gf ⧸ D.H)) := by simp [Dat.HtY, Dat.Ht]
    rw [← h1, ← hy'', h2 _ e01_ne b _, hvb, h3 _ e01_ne _ hb11, e1]
  have hP0 : 0 ≤ ∏ v, |((D.act b ((γ₀ : PG F) • y).2) v).1.im| :=
      Finset.prod_nonneg fun _ _ => abs_nonneg _
  have hK := single_le_sum (f := fun x => max (C' x) 0 * (1 + 1 / D.hf ![0,
                                                                         1] (D.rep (x : Gf ⧸ D.H))))
    (fun x _ => mul_nonneg (le_max_right _ _) (add_nonneg zero_le_one (div_nonneg zero_le_one (hapos x).le))) hx'S
  have ha := hapos x'
  have h1P : 1 + ∏ v, |((D.act b ((γ₀ : PG F) • y).2) v).1.im| ≤ (1 + 1 / D.hf ![0,
                                                                                 1] (D.rep (x' : Gf ⧸ D.H))) * (1 + D.HtY s y) := by
    rw [eq_div_of_mul_eq ha.ne' hHt]; have : 0 ≤ 1 / D.hf ![0,
                                                            1] (D.rep (x' : Gf ⧸ D.H)) := by positivity
    nlinarith [show (1 + 1 / D.hf ![0,
                                    1] (D.rep (x' : Gf ⧸ D.H))) * (1 + D.HtY s y) - (1 + D.HtY s y / D.hf ![0, 1] (D.rep (x' : Gf ⧸ D.H))) = D.HtY s y + 1 / D.hf ![0, 1] (D.rep (x' : Gf ⧸ D.H)) by ring]
  change ((A y).ncard : ℝ) ≤ _
  rw [← hfin0.2, ← hfin1.2, hy'']
  have hM0 : 0 ≤ max (C' x') 0 := le_max_right _ _
  have hle' : ((A ((((x' : Gf ⧸ D.H) : D.Om), D.act b ((γ₀ : PG F) • y).2) : D.Y)).ncard : ℝ) ≤
      max (C' x') 0 * (1 + ∏ v, |((D.act b ((γ₀ : PG F) • y).2) v).1.im|) :=
    hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  nlinarith [mul_le_mul_of_nonneg_left h1P hM0,
             mul_le_mul_of_nonneg_right hK (by linarith : 0 ≤ 1 + D.HtY s y)]

-- === UpperHalfPlaneMeasureCoordinates ===

lemma pt_cont : Continuous (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) :=
  Continuous.subtype_mk (by fun_prop) _

lemma pt_bij : Bijective (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) :=
  ⟨fun ⟨x, y, hy⟩ ⟨x', y', hy'⟩ h => by
    have h' : (y : ℂ) * (x + I) = (y' : ℂ) * (x' + I) := congrArg Subtype.val h
    have him := congrArg im h'; have hre := congrArg re h'; simp at him hre; subst him
    have := mul_left_cancel₀ hy hre; subst this; rfl,
   fun ⟨z, hz⟩ => ⟨(z.re / z.im, ⟨z.im, hz⟩),
                   Subtype.ext $ Complex.ext (by simp [pt]; field_simp) (by simp [pt])⟩⟩

lemma lint_comap {α : Type} [MeasurableSpace α] {p : α → Prop} (hp : MeasurableSet {a | p a}) (μ : Measure α) (f : α → ℝ≥0∞) :
    ∫⁻ x : {a // p a}, f x.1 ∂(Measure.comap Subtype.val μ) = ∫⁻ x in {a | p a}, f x ∂μ :=
  lintegral_subtype_comap hp f

lemma sf_nz : SigmaFinite (Measure.comap (Subtype.val : {y : ℝ // y ≠ 0} → ℝ) volume) := by
  have hY : MeasurableSet {y : ℝ | y ≠ 0} := (measurableSet_singleton 0).compl
  have hm := (MeasurableEmbedding.subtype_coe hY).map_comap (μ := (volume : Measure ℝ))
  exact SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable (by convert (inferInstance : SigmaFinite ((volume : Measure ℝ).restrict (range (Subtype.val : {y : ℝ // y ≠ 0} → ℝ)))) <;> exact hm)

lemma pt_mp : MeasurePreserving (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2)
    ((volume : Measure ℝ).prod ((Measure.comap Subtype.val volume).withDensity fun y => oR (1 / |y.1|))) volume := by
  let Ψ (x y : ℝ) : ℂ := (y : ℂ) * (x + I)
  have hS :=
      isOpen_U_jl.measurableSet; have hY : MeasurableSet {y : ℝ | y ≠ 0} := (measurableSet_singleton 0).compl
  have hemb := MeasurableEmbedding.subtype_coe hS
  have := sf_nz
  refine ⟨pt_cont.measurable, Measure.ext fun s hs => ?_⟩
  let G : ℂ → ℝ≥0∞ := (Subtype.val '' s).indicator 1
  have hGm : Measurable G := measurable_one.indicator (hemb.measurableSet_image.2 hs)
  have hGv (z : P) : G z.1 = s.indicator 1 z := by
    have hz : z.1 ∈ Subtype.val '' s ↔ z ∈ s := ⟨fun ⟨_, hw, e⟩ => Subtype.ext e ▸ hw, fun h => ⟨z,
                                                                                                 h, rfl⟩⟩
    by_cases h : z ∈ s <;> simp [G, indicator, hz, h]
  rw [Measure.map_apply pt_cont.measurable hs, ← lintegral_indicator_one (pt_cont.measurable hs),
    show ((fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) ⁻¹' s).indicator 1 = fun p => G (Ψ p.1 p.2.1) from
      funext fun p => (hGv (pt p.1 p.2.1 p.2.2)).symm,
    lintegral_prod (fun p : ℝ × {y : ℝ // y ≠ 0} => G (Ψ p.1 p.2.1))
      (hGm.comp (by fun_prop : Continuous fun p : ℝ × {y : ℝ // y ≠ 0} => Ψ p.1 p.2.1).measurable).aemeasurable]
  have e2 x : ∫⁻ y, G (Ψ x y.1) ∂((Measure.comap Subtype.val volume).withDensity fun y : {y : ℝ // y ≠ 0} => oR (1 / |y.1|))
      = ∫⁻ y, oR (1 / |y|) * G (Ψ x y) := by
    have hf : Measurable fun y : {y : ℝ // y ≠ 0} => G (Ψ x y.1) := hGm.comp (by fun_prop)
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf]
    simpa only [Pi.mul_apply, show ({y : ℝ | y ≠ 0} : Set ℝ) = {0}ᶜ from rfl,
                restrict_compl_singleton] using
      lint_comap hY (volume : Measure ℝ) (fun y => oR (1 / |y|) * G (Ψ x y))
  simp_rw [e2]
  have hkey : ∫⁻ x, ∫⁻ y, oR (1 / |y|) * G (Ψ x y) = ∫⁻ z, oR (1 / z.im ^ 2) * G z := by
    rw [lintegral_lintegral_swap ((ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hGm.comp (by fun_prop : Continuous fun p : ℝ × ℝ => Ψ p.1 p.2).measurable)).aemeasurable]
    have hR : ∫⁻ z, oR (1 / z.im ^ 2) * G z = ∫⁻ y : ℝ, ∫⁻ u : ℝ, oR (1 / y ^ 2) * G ((u : ℂ) + y * I) := by
      have hmg : Measurable fun p : ℝ × ℝ => oR (1 / (measurableEquivRealProd.symm p).im ^ 2) * G (measurableEquivRealProd.symm p) :=
        ((ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun z : ℂ => 1 / z.im ^ 2)).mul hGm).comp (MeasurableEquiv.measurable _)
      rw [← Complex.volume_preserving_equiv_real_prod.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
        Measure.volume_eq_prod, lintegral_prod_symm _ hmg.aemeasurable]
      congr 1; funext y; congr 1; funext u; simp only [Complex.measurableEquivRealProd]; congr 2; exact mk_eq_add_mul_I u y
    rw [hR]; congr 1; funext y
    have hmx : Measurable fun x : ℝ => G (Ψ x y) := hGm.comp (by fun_prop)
    have hmu : Measurable (fun u : ℝ => G ((u : ℂ) + y * I)) :=
        hGm.comp (by fun_prop : Continuous fun u : ℝ => (u : ℂ) + y * I).measurable
    rw [lintegral_const_mul _ hmx, lintegral_const_mul _ hmu]
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have hsc : ∫⁻ x, G (Ψ x y) = oR |y⁻¹| * ∫⁻ u : ℝ, G ((u : ℂ) + y * I) := by
        calc _ = ∫⁻ x : ℝ, G (((y * x : ℝ) : ℂ) + y * I) :=
            by congr 1; funext x; congr 1; simp [Ψ]; ring
          _ = ∫⁻ u : ℝ, G ((u : ℂ) + y * I) ∂(Measure.map (y * ·) volume) :=
              (lintegral_map hmu (measurable_const_mul y)).symm
          _ = _ := by rw [Real.map_volume_mul_left hy, lintegral_smul_measure, smul_eq_mul]
      rw [hsc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        show 1 / |y| * |y⁻¹| = 1 / y ^ 2 by rw [abs_inv, one_div, one_div, ← mul_inv, ← sq, sq_abs]]
  rw [hkey]
  let s' : Set {z : ℂ // z.im ≠ 0} := s
  have hs' : MeasurableSet s' := hs
  change _ = (Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume).withDensity (fun z => oR (1 / z.1.im ^ 2)) s'
  rw [withDensity_apply _ hs', ← lintegral_indicator hs',
    show s'.indicator (fun z : {z : ℂ // z.im ≠ 0} => oR (1 / z.1.im ^ 2)) = fun z => oR (1 / z.1.im ^ 2) * G z.1 from
      funext fun z => by
        rw [hGv z, show s.indicator (1 : P → ℝ≥0∞) z = s'.indicator (fun _ => 1) z from rfl]
        by_cases h : z ∈ s' <;> simp [indicator, h],
    lint_comap hS (volume : Measure ℂ) (fun z => oR (1 / z.im ^ 2) * G z), ← lintegral_indicator hS]
  congr 1; funext z; by_cases h : z.im ≠ 0
  · simp [indicator, h]
  · simp [indicator, h, G, show z ∉ Subtype.val '' s from fun ⟨w, _, hw⟩ => h (hw ▸ w.2)]

theorem upper_half_plane_measure_coordinates_jl : UpperHalfPlaneMeasureCoordinates := ⟨pt_mp,
                                                                                       pt_bij, pt_cont⟩

-- === B6: Hyperbolic ball volume / kernel L¹ integrability ===

theorem hyperbolic_ball_volume_proof_jl : B1a → B1b → B1c → UpperHalfPlaneMeasureCoordinates → B6 := by
  intro _ _ _ _ k hk
  let F (y : ℝ) := (1 + y ^ (-(1 / 2 : ℝ))) / (1 + y) ^ 2
  have hFint : IntegrableOn F (Ioi 0) := by
    have hm : Measurable F := by unfold F; fun_prop
    have h1 : IntegrableOn F (Ioo 0 2) :=
      ((integrableOn_const (C := (1 : ℝ)) (hs := by simp)).add
        ((intervalIntegral.integrableOn_Ioo_rpow_iff (s := -(1 / 2 : ℝ)) (by norm_num)).2 (by norm_num))).mono'
        hm.aestronglyMeasurable $ (ae_restrict_iff' measurableSet_Ioo).2 $ Eventually.of_forall fun y hy => by
          have hy0 : 0 < y := hy.1; have := rpow_nonneg hy0.le (-(1 / 2 : ℝ))
          rw [Real.norm_eq_abs, abs_of_nonneg (by unfold F; positivity)]; unfold F
          dsimp only [Pi.add_apply]; rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg y]
    have h2 : IntegrableOn F (Ioi 1) :=
      ((integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) one_pos).const_mul 2).mono'
        hm.aestronglyMeasurable $ (ae_restrict_iff' measurableSet_Ioi).2 $ Eventually.of_forall fun y (hy : 1 < y) => by
          have hy0 : 0 < y := by linarith
          have hp := rpow_le_one_of_one_le_of_nonpos hy.le (z := -(1 / 2 : ℝ)) (by norm_num)
          have hp0 := rpow_nonneg hy0.le (-(1 / 2 : ℝ))
          rw [Real.norm_eq_abs, abs_of_nonneg (by unfold F; positivity),
            show y ^ (-2 : ℝ) = 1 / y ^ 2 by rw [rpow_neg hy0.le, one_div]; norm_cast]
          unfold F; rw [div_le_iff₀ (by positivity)]
          have : 2 ≤ 2 * (1 / y ^ 2) * (1 + y) ^ 2 := by rw [mul_one_div, div_mul_eq_mul_div,
                                                             le_div_iff₀ (by positivity)]; nlinarith
          linarith
    exact (h1.union h2).mono_set fun y hy => if h : y < 2 then Or.inl ⟨hy,
                                                                       h⟩ else Or.inr (show 1 < y by linarith [show (0 : ℝ) < y from hy])
  let A : ℝ≥0∞ := ∫⁻ x : ℝ, oR ((1 + x ^ 2)⁻¹)
  let H (w : P) : ℝ≥0∞ := oR (kap iP w ^ 2 * (1 + |w.1.im| ^ (-(1 / 2 : ℝ))))
  let B (y : ℝ) : ℝ≥0∞ :=
      if 0 < y then oR (16 * y ^ 2 / (1 + y) ^ 2 * (1 + y ^ (-(1 / 2 : ℝ)))) * (oR y⁻¹ * A) else 0
  have hHm : Measurable H := ENNReal.measurable_ofReal.comp
    (((cont_kap.comp (continuous_const.prodMk continuous_id)).measurable.pow_const 2).mul
      (measurable_const.add ((continuous_im.comp continuous_subtype_val).abs.measurable.pow_const
        (-(1 / 2 : ℝ)))))
  have hfin : ∫⁻ w, H w < ∞ := by
    have hY : MeasurableSet {y : ℝ | y ≠ 0} := (measurableSet_singleton 0).compl
    have := sf_nz
    rw [← pt_mp.lintegral_comp hHm,
      lintegral_prod_symm (fun p : ℝ × {y : ℝ // y ≠ 0} => H (pt p.1 p.2.1 p.2.2)) (hHm.comp pt_cont.measurable).aemeasurable]
    have hinner (y : ℝ) (hy : y ≠ 0) : ∫⁻ x : ℝ, H (pt x y hy) ≤ B y := by
      rcases lt_or_gt_of_ne hy with hn | hp
      · simp [H, kap, iP, pt, not_lt.2 hn.le]
      · have hx : ∫⁻ x : ℝ, oR ((1 + (y * x) ^ 2)⁻¹) = oR y⁻¹ * A := by
          rw [← lintegral_map (by fun_prop : Measurable fun x : ℝ => oR ((1 + x ^ 2)⁻¹)) (measurable_const_mul y),
            Real.map_volume_mul_left hp.ne', lintegral_smul_measure, smul_eq_mul, abs_of_pos (inv_pos.2 hp)]
        dsimp only [B]; rw [ite_eq_left hp, ← hx, ← lintegral_const_mul _ (by fun_prop)]
        refine lintegral_mono fun x => by
          dsimp only [H]; rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hkap : kap iP (pt x y hp.ne') = 4 * y / ((y * x) ^ 2 + (1 + y) ^ 2) := by
            rw [kap, ite_eq_left (by simp [iP, pt, hp]), nsq_sub_conj]; simp [iP, pt]
          have hsq : kap iP (pt x y hp.ne') ^ 2 ≤ 16 * y ^ 2 / (1 + y) ^ 2 * (1 + (y * x) ^ 2)⁻¹ := by
            rw [hkap,
                show 16 * y ^ 2 / (1 + y) ^ 2 * (1 + (y * x) ^ 2)⁻¹ = (4 * y) ^ 2 / ((1 + (y * x) ^ 2) * (1 + y) ^ 2) by field_simp; ring, div_pow]
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) $ by
              nlinarith [sq_nonneg ((y * x) ^ 2),
                         mul_nonneg (sq_nonneg (y * x)) (sq_nonneg (1 + y)),
                mul_nonneg (sq_nonneg (1 + y)) (show (0 : ℝ) ≤ (1 + y) ^ 2 - 1 by nlinarith)]
          have : |(pt x y hp.ne').1.im| = y := by simp [pt, abs_of_pos hp]
          rw [this]; have := rpow_nonneg hp.le (-(1 / 2 : ℝ))
          calc _ ≤ 16 * y ^ 2 / (1 + y) ^ 2 * (1 + (y * x) ^ 2)⁻¹ * (1 + y ^ (-(1 / 2 : ℝ))) :=
              mul_le_mul_of_nonneg_right hsq (by positivity)
            _ = _ := by ring
    calc _ ≤ ∫⁻ y : {y : ℝ // y ≠ 0}, B y.1 ∂((Measure.comap Subtype.val volume).withDensity fun y => oR (1 / |y.1|)) :=
          lintegral_mono fun y => hinner y.1 y.2
      _ = ∫⁻ y in {y : ℝ | y ≠ 0}, oR (1 / |y|) * B y := by
          have hBm : Measurable fun y : {y : ℝ // y ≠ 0} => B y.1 :=
            (Measurable.ite measurableSet_Ioi (by fun_prop : Measurable fun y : ℝ => oR (16 * y ^ 2 / (1 + y) ^ 2 * (1 + y ^ (-(1 / 2 : ℝ)))) * (oR y⁻¹ * A)) measurable_const).comp measurable_subtype_coe
          rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hBm]
          exact lint_comap hY (volume : Measure ℝ) (fun y => oR (1 / |y|) * B y)
      _ ≤ ∫⁻ y, (Set.Ioi (0 : ℝ)).indicator (fun y => oR (16 * F y) * A) y :=
          (setLIntegral_le_lintegral _ _).trans $ lintegral_mono fun y => by
          by_cases hy : 0 < y
          · rw [indicator_of_mem (show y ∈ Set.Ioi (0 : ℝ) from hy)]; dsimp only [B]
            rw [ite_eq_left hy, abs_of_pos hy, ← mul_assoc, ← mul_assoc,
              ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            exact le_of_eq $ congrArg (· * A) $ congrArg oR $ by unfold F; field_simp
          · simp [B, hy]
      _ = (∫⁻ y in Ioi (0 : ℝ), oR (16 * F y)) * A := by rw [lintegral_indicator measurableSet_Ioi,
                                                             lintegral_mul_const _ (by unfold F; fun_prop)]
      _ < ∞ := ENNReal.mul_lt_top (hFint.const_mul 16).lintegral_lt_top integrable_inv_one_add_sq.lintegral_lt_top
  have hrp {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : t ^ ((k : ℝ) / 2) ≤ t ^ 2 := by
    have hk2 : (2 : ℝ) ≤ (k : ℝ) / 2 := by have : (4 : ℝ) ≤ k := (by exact_mod_cast hk); linarith
    rcases h0.eq_or_lt with rfl | ht
    · rw [zero_rpow (by linarith)]; positivity
    · simpa using rpow_le_rpow_of_exponent_ge ht h1 hk2
  refine ⟨(∫⁻ w, H w).toNNReal, fun z => ?_⟩
  rw [ENNReal.coe_toNNReal hfin.ne]
  obtain ⟨g, hg0, hg1, rfl⟩ := trans_iP z
  have him (w : P) : (g • w).1.im = g.val.det * w.1.im := by
    rw [im_smul_jl, show den g w.1 = 1 by simp [den, hg0, hg1], normSq_one, div_one]
  have hkc (u : P) : Continuous (kap u) := cont_kap.comp (continuous_const.prodMk continuous_id)
  have hima : Measurable fun w : P => |w.1.im| :=
      (continuous_im.comp continuous_subtype_val).abs.measurable
  refine ⟨?_, ?_⟩
  · rw [← (mp_smul_P g).lintegral_comp (f := fun w : P => oR (kap (g • iP) w ^ ((k : ℝ) / 2)))
      (ENNReal.measurable_ofReal.comp ((hkc _).measurable.pow_const _))]
    refine lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_
    rw [kap_smul_jl]
    exact (hrp (kap_nonneg_jl iP w) (kap_le_one iP w)).trans $
      le_mul_of_one_le_right (sq_nonneg _) (by linarith [rpow_nonneg (abs_nonneg w.1.im) (-(1 / 2 : ℝ))])
  · rw [← (mp_smul_P g).lintegral_comp (f := fun w : P => oR (kap (g • iP) w ^ ((k : ℝ) / 2) * (|(g • iP).1.im| / |w.1.im|) ^ ((1 : ℝ) / 2)))
      (ENNReal.measurable_ofReal.comp (((hkc _).measurable.pow_const _).mul ((measurable_const.div hima).pow_const _)))]
    refine lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_
    rw [kap_smul_jl, him, him, show |g.val.det * iP.1.im| / |g.val.det * w.1.im| = |w.1.im|⁻¹ by
        rw [show iP.1.im = 1 by simp [iP], mul_one, abs_mul, div_mul_eq_div_div,
            div_self (abs_ne_zero.2 g.det_ne_zero), one_div],
      inv_rpow (abs_nonneg _), ← rpow_neg (abs_nonneg _)]
    have hp0 := rpow_nonneg (abs_nonneg w.1.im) (-(1 / 2 : ℝ))
    exact (mul_le_mul_of_nonneg_right (hrp (kap_nonneg_jl iP w) (kap_le_one iP w)) hp0).trans $
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)

end UpperTheory.Esk

-- ==== B1

noncomputable section

open MeasureTheory Matrix Finset Filter Function Subgroup MulAction QuotientGroup
open Set hiding center
open Real hiding dist_eq
open _root_.Complex hiding log exp exp_add exp_neg exp_log exp_nat_mul log_mul log_exp exp_sub
open scoped ENNReal NNReal ComplexConjugate Classical Real

namespace UpperTheory.Esk

-- === Shared algebraic & analytic lemmas (reused across B1..B5) ===

lemma j1_one (k : ℕ) (z : P) : j1 k 1 z = 1 := by simp [j1, den]

lemma j1_scalar (k : ℕ) (g : GL2 ℝ) (hb : g 0 1 = 0) (hc : g 1 0 = 0) (h : g 0 0 = g 1 1) (z : P) :
    j1 k g z = ((SignType.sign (g 0 0) : ℝ) : ℂ) ^ k := by
  have ha : g 0 0 ≠ 0 := fun h0 => g.det_ne_zero (by simp [det_eq, hb, hc, h0, ← h])
  have hdet : |g.val.det| = |g 0 0| ^ 2 := by rw [det_eq, hb, hc, ← h]; simp [sq, abs_mul]
  have hr : |g.val.det| ^ (-(k : ℝ) / 2) = (|g 0 0| ^ k)⁻¹ := by
    rw [hdet, neg_div, rpow_neg (sq_nonneg _), sq_rpow_half (abs_nonneg _)]
  have hkey : g 0 0 ^ k * (|g 0 0| ^ k)⁻¹ = (SignType.sign (g 0 0) : ℝ) ^ k := by
    rw [show g 0 0 ^ k = (SignType.sign (g 0 0) : ℝ) ^ k * |g 0 0| ^ k by rw [← mul_pow,
                                                                              sign_mul_abs],
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (abs_ne_zero.2 ha)), mul_one]
  calc j1 k g z = ((g 0 0 ^ k * (|g 0 0| ^ k)⁻¹ : ℝ) : ℂ) := by
        simp [j1, den, hc, h, hr]
    _ = _ := by rw [hkey, ofReal_pow]

lemma qj_conj (k : ℕ) (G g : GL2 ℝ) (w : P) :
    q1 k (G • w) (G • g • w) * j1 k (G * g * G⁻¹) (G • w) = q1 k w (g • w) * j1 k g w := by
  have hAB : j1 k G⁻¹ (G • w) * j1 k G w = 1 := by rw [← j1_mul, inv_mul_cancel, j1_one]
  have e1 : j1 k (G * g * G⁻¹) (G • w) = j1 k G (g • w) * j1 k g w * j1 k G⁻¹ (G • w) := by
    rw [j1_mul, inv_smul_smul, j1_mul]
  rw [e1]
  linear_combination (j1 k g w * j1 k G⁻¹ (G • w)) * q1_smul k G w (g • w) + (q1 k w (g • w) * j1 k g w) * hAB

lemma norm_qj_jl (k : ℕ) (hk : 1 ≤ k) (g : GL2 ℝ) (z : P) :
    ‖q1 k z (g • z) * j1 k g z‖ = ((k : ℝ) - 1) / (4 * π) * kap z (g • z) ^ ((k : ℝ) / 2) := by
  have ha : 0 < |z.1.im| ^ ((k : ℝ) / 2) := rpow_pos_of_pos (abs_pos.2 z.2) _
  have hb : 0 < |(g • z).1.im| ^ ((k : ℝ) / 2) := rpow_pos_of_pos (abs_pos.2 (g • z).2) _
  rw [norm_mul]
  apply mul_right_cancel₀ (mul_pos ha hb).ne'
  calc ‖q1 k z (g • z)‖ * ‖j1 k g z‖ * (|z.1.im| ^ ((k : ℝ) / 2) * |(g • z).1.im| ^ ((k : ℝ) / 2))
      = (‖q1 k z (g • z)‖ * |z.1.im| ^ ((k : ℝ) / 2)) * (‖j1 k g z‖ * |(g • z).1.im| ^ ((k : ℝ) / 2)) :=
          by ring
    _ = _ := by rw [norm_j1, norm_q1 k z (g • z) hk]; ring

lemma nrm_pos_jl {I : Type} [Fintype I] (k : I → ℕ) (z : X I) : 0 < nrm k z :=
  Finset.prod_pos fun v _ => rpow_pos_of_pos (abs_pos.2 (z v).2) _

lemma nrm_nonneg_jl {I : Type} [Fintype I] (k : I → ℕ) (z : X I) : 0 ≤ nrm k z :=
    (nrm_pos_jl k z).le

lemma Kap_nonneg_jl {I : Type} [Fintype I] (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun _ _ => rpow_nonneg (kap_nonneg_jl _ _) _

lemma Kap_symm_jl {I : Type} [Fintype I] (k : I → ℕ) (z w : X I) : Kap k z w = Kap k w z :=
  Finset.prod_congr rfl fun v _ => by rw [kap_symm]

def cst_jl {I : Type} [Fintype I] (k : I → ℕ) : ℝ := ∏ v, ((k v : ℝ) - 1) / (4 * π)

lemma cst_nonneg_jl {I : Type} [Fintype I] (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) : 0 ≤ cst_jl k :=
  Finset.prod_nonneg fun v _ => div_nonneg (by have : (1 : ℝ) ≤ k v := (by exact_mod_cast hk v); linarith) (by positivity)

lemma norm_qq_jl {I : Type} [Fintype I] (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (z w : X I) :
    ‖qq k z w‖ * nrm k z = cst_jl k * Kap k z w * nrm k w := by
  simp only [qq, nrm, Kap, cst_jl, norm_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => norm_q1 (k v) (z v) (w v) (hk v)

lemma vecMul_ne_jl {F : Type} [Field F] {s : Fin 2 → F} (hs : s ≠ 0) (γ : GL2 F) : s ᵥ* γ.val ≠ 0 :=
    fun h => hs $ by
  have := congrArg (· ᵥ* (γ⁻¹ : GL2 F).val) h
  simpa [Matrix.vecMul_vecMul] using this

lemma fix_mk_jl {F : Type} [Field F] (t : Fin 2 → F) (g : GL2 F) : Fix t (g : PG F) ↔ ∃ c : F, t ᵥ* g.val = c • t := by
  obtain ⟨ζ, e⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL2 F)) g
  obtain ⟨h1, h2, h3⟩ := center_entries ζ.2
  have hl : ζ.1 0 0 ≠ 0 := fun h0 => ζ.1.det_ne_zero (by rw [det_fin_two, h1, ← h3, h0]; ring)
  have hv (u : Fin 2 → F) : u ᵥ* ζ.1.val = ζ.1 0 0 • u := funext fun i => by
    fin_cases i <;> simp [vecMul, dotProduct, Fin.sum_univ_two, h1, h2, h3, mul_comm]
  unfold Fix; rw [e, Units.val_mul, ← vecMul_vecMul, hv]
  exact ⟨fun ⟨c, hc⟩ => ⟨(ζ.1 0 0)⁻¹ * c, by rw [mul_smul, ← hc, smul_smul, inv_mul_cancel₀ hl,
                                                 one_smul]⟩,
    fun ⟨c, hc⟩ => ⟨ζ.1 0 0 * c, by rw [hc, smul_smul]⟩⟩

lemma fix_conj_jl {F : Type} [Field F] (s : Fin 2 → F) (γ δ : GL2 F) :
    Fix s ((δ : PG F) * γ * (δ : PG F)⁻¹) ↔ ∃ c : F, (s ᵥ* δ.val) ᵥ* γ.val = c • (s ᵥ* δ.val) := by
  rw [show (δ : PG F) * γ * (δ : PG F)⁻¹ = ((δ * γ * δ⁻¹ : GL2 F) : PG F) by simp, fix_mk_jl]
  refine exists_congr fun c => ?_
  simp only [Units.val_mul, ← vecMul_vecMul]
  exact ⟨fun h => by have := congrArg (· ᵥ* δ.val) h; simpa [vecMul_vecMul, smul_vecMul] using this,
    fun h => by have := congrArg (· ᵥ* (δ⁻¹ : GL2 F).val) h; simpa [vecMul_vecMul,
                                                                    smul_vecMul] using this⟩

lemma row_exists {F : Type} [Field F] (s : Fin 2 → F) (hs : s ≠ 0) : ∃ γ : GL2 F, ![0,
                                                                                    1] ᵥ* γ.val = s := by
  by_cases h0 : s 0 = 0
  · have h1 : s 1 ≠ 0 := fun h1 => hs (funext fun i => by fin_cases i <;> simp [h0, h1])
    exact ⟨GeneralLinearGroup.mkOfDetNeZero !![1, 0; s 0, s 1] (by simp [det_fin_two_of, h1]),
      funext fun i => by fin_cases i <;> simp [vecMul, dotProduct, Fin.sum_univ_two]⟩
  · exact ⟨GeneralLinearGroup.mkOfDetNeZero !![0, 1; s 0, s 1] (by simp [det_fin_two_of, h0]),
      funext fun i => by fin_cases i <;> simp [vecMul, dotProduct, Fin.sum_univ_two]⟩

section DatLemmas
variable {F I Gf ι : Type} [Field F] [Group Gf] (D : Dat F I Gf)

lemma r_det_jl (v : I) (γ : GL2 F) : (D.r v γ).val.det = D.σ v γ.val.det := by
  rw [det_fin_two, det_fin_two, map_sub, map_mul, map_mul]; rfl

lemma r_tr (v : I) (γ : GL2 F) : (D.r v γ).val.trace = D.σ v γ.val.trace := by
  rw [trace_fin_two, trace_fin_two, map_add]; rfl

lemma ee_mul_left_jl (h : D.H) (u : Gf) : D.ee (h * u) = D.χ h * D.ee u := by
  unfold Dat.ee; by_cases hu : u ∈ D.H
  · rw [dite_eq_left (D.H.mul_mem h.2 hu),
        dite_eq_left hu]; exact congrArg Units.val (map_mul D.χ h ⟨u, hu⟩)
  · rw [dite_eq_right (fun hm => hu (by simpa using D.H.mul_mem (D.H.inv_mem h.2) hm)),
        dite_eq_right hu, mul_zero]

lemma ee_mul_right_jl (u : Gf) (h : D.H) : D.ee (u * h) = D.ee u * D.χ h := by
  unfold Dat.ee; by_cases hu : u ∈ D.H
  · rw [dite_eq_left (D.H.mul_mem hu h.2),
        dite_eq_left hu]; exact congrArg Units.val (map_mul D.χ ⟨u, hu⟩ h)
  · rw [dite_eq_right (fun hm => hu (by simpa using D.H.mul_mem hm (D.H.inv_mem h.2))),
        dite_eq_right hu, zero_mul]

lemma ee_inv_mul_jl (h : D.H) (u : Gf) : D.ee ((h : Gf)⁻¹ * u) = (D.χ h : ℂ)⁻¹ * D.ee u := by
  simpa [Units.val_inv_eq_inv_val] using ee_mul_left_jl D h⁻¹ u

lemma ee_one_jl : D.ee 1 = 1 :=
    by unfold Dat.ee; rw [dite_eq_left D.H.one_mem]; exact congrArg Units.val (map_one D.χ)

lemma smul_center_jl (v : I) (c : GL2 F) (hc : c ∈ Subgroup.center (GL2 F)) (w : P) : D.r v c • w = w := by
  obtain ⟨h1, h2, h3⟩ := center_entries hc
  exact center_smul _ (by change D.σ v (c 0 1) = 0; rw [h1, map_zero])
    (by change D.σ v (c 1 0) = 0; rw [h2,
                                      map_zero]) (by change D.σ v (c 0 0) = D.σ v (c 1 1); rw [h3]) w

lemma act_center_jl (c : GL2 F) (hc : c ∈ Subgroup.center (GL2 F)) (z : X I) : D.act c z = z :=
  funext fun v => smul_center_jl D v c hc (z v)

lemma act_mul_jl (g h : GL2 F) (z : X I) : D.act (g * h) z = D.act g (D.act h z) :=
  funext fun v => by change D.r v (g * h) • z v = _; rw [map_mul, mul_smul]; rfl

lemma smulO_out_jl (γ : PG F) (ω : D.Om) : γ • ω = ((D.j γ.out * D.rep ω : Gf) : Gf ⧸ D.H) := by
  conv_lhs => rw [← QuotientGroup.out_eq' γ, ← QuotientGroup.out_eq' ω]
  exact D.mk_smulO γ.out (D.rep ω)

lemma smulX_out_jl (γ : PG F) (w : D.Xs) : (γ • w : D.Xs) = D.act γ.out w := by
  conv_lhs => rw [← QuotientGroup.out_eq' γ]
  exact D.mk_smulX γ.out w

variable [Fintype I]

lemma norm_ee_le_jl (hx : D.Ax) (u : Gf) : ‖D.ee u‖ ≤ 1 := by
  unfold Dat.ee; split_ifs with hu; exact (hx.χn _).le; simp

lemma J_mul_jl (k : I → ℕ) (g h : GL2 F) (w : X I) : D.J k (g * h) w = D.J k g (D.act h w) * D.J k h w := by
  simp only [Dat.J, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => by rw [map_mul]; exact j1_mul _ _ _ _

lemma J_center_jl (k : I → ℕ) (hC : D.Compat k) (c : GL2 F) (hc : c ∈ Subgroup.center (GL2 F)) (w : X I) :
    D.J k c w = D.χ ⟨D.j c, D.cenH c hc⟩ := by
  rw [hC c hc]; obtain ⟨h1, h2, h3⟩ := center_entries hc
  exact Finset.prod_congr rfl fun v _ => j1_scalar (k v) (D.r v c)
    (by change D.σ v (c 0 1) = 0; rw [h1, map_zero]) (by change D.σ v (c 1 0) = 0; rw [h2,
                                                                                       map_zero])
    (by change D.σ v (c 0 0) = D.σ v (c 1 1); rw [h3]) (w v)

lemma Kap_smul_jl (k : I → ℕ) (δ : PG F) (z w : D.Xs) : Kap k (δ • z : D.Xs) (δ • w : D.Xs) = Kap k z w :=
  Finset.prod_congr rfl fun v _ => by rw [kap_smulX]

lemma Kap_swap_jl (k : I → ℕ) (γ : PG F) (z w : D.Xs) : Kap k z (γ • w : D.Xs) = Kap k w (γ⁻¹ • z : D.Xs) := by
  rw [← Kap_smul_jl D k γ⁻¹ z (γ • w), inv_smul_smul]; exact Kap_symm_jl k _ _

lemma norm_qJ_jl (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (g : GL2 F) (z w : X I) :
    ‖qq k z (D.act g w) * D.J k g w‖ * nrm k z = cst_jl k * Kap k z (D.act g w) * nrm k w := by
  simp only [qq, Dat.J, Dat.act, nrm, Kap, cst_jl, norm_mul, norm_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have h1 := norm_q1 (k v) (z v) (D.r v g • w v) (hk v)
  have h2 := norm_j1 (k v) (D.r v g) (w v)
  calc ‖q1 (k v) (z v) (D.r v g • w v)‖ * ‖j1 (k v) (D.r v g) (w v)‖ * |(z v).1.im| ^ ((k v : ℝ) / 2)
      = (‖q1 (k v) (z v) (D.r v g • w v)‖ * |(z v).1.im| ^ ((k v : ℝ) / 2)) * ‖j1 (k v) (D.r v g) (w v)‖ :=
          by ring
    _ = _ := by rw [h1, ← h2]; ring

-- === KernelTermsInvariantBounded ===

lemma norm_Te_le_jl [Fintype ι] (hx : D.Ax) (a : ι → Gf) (γ : GL2 F) (x : Gf) : ‖D.Te a γ x‖ ≤ Fintype.card ι :=
  (norm_sum_le _ _).trans $ (Finset.sum_le_sum fun _ _ => norm_ee_le_jl D hx _).trans (by simp)

lemma kt_mul_center_jl [Fintype ι] (k : I → ℕ) (a : ι → Gf) (hC : D.Compat k) (γ c : GL2 F)
    (hc : c ∈ Subgroup.center (GL2 F)) (z : X I) (x : Gf) : D.kt k a (γ * c) z x = D.kt k a γ z x := by
  have hT : D.Te a (γ * c) x = (D.χ ⟨D.j c, D.cenH c hc⟩ : ℂ)⁻¹ * D.Te a γ x := by
    rw [Dat.Te, Dat.Te, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc' := Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ (D.cenC c hc)) x⁻¹
    rw [show x⁻¹ * (D.j (γ * c))⁻¹ * x * a i = (D.j c)⁻¹ * (x⁻¹ * (D.j γ)⁻¹ * x * a i) by
      rw [map_mul, _root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, ← mul_assoc, hc']; group]
    exact ee_inv_mul_jl D ⟨D.j c, D.cenH c hc⟩ _
  unfold Dat.kt; rw [act_mul_jl, act_center_jl D c hc, J_mul_jl, act_center_jl D c hc,
                     J_center_jl D k hC c hc, hT]
  have hne : (D.χ ⟨D.j c, D.cenH c hc⟩ : ℂ) ≠ 0 := Units.ne_zero _
  linear_combination (D.Te a γ x * (qq k z (D.act γ z) * D.J k γ z)) * inv_mul_cancel₀ hne

lemma kt_mul_H_jl [Fintype ι] (k : I → ℕ) (a : ι → Gf) (hG : D.Good a) (γ : GL2 F) (z : X I) (x : Gf) (h : D.H) :
    D.kt k a γ z (x * h) = D.kt k a γ z x := by
  have key := hG (fun y => D.ee ((x⁻¹ * (D.j γ)⁻¹ * x) * y))
    (fun y h' => by rw [← mul_assoc, ee_mul_right_jl, mul_comm]) 1 h
  simp only [one_mul] at key
  unfold Dat.kt; congr 1; unfold Dat.Te
  have e1 i : (x * ↑h)⁻¹ * (D.j γ)⁻¹ * (x * ↑h) * a i = (h : Gf)⁻¹ * ((x⁻¹ * (D.j γ)⁻¹ * x) * (h * a i)) :=
      by group
  rw [Finset.sum_congr rfl fun i _ => by rw [e1, ee_inv_mul_jl], ← Finset.mul_sum, key, ← mul_assoc,
      inv_mul_cancel₀ (Units.ne_zero _), one_mul]

lemma kt_conj_jl [Fintype ι] (k : I → ℕ) (a : ι → Gf) (d g : GL2 F) (z : X I) (x : Gf) :
    D.kt k a (d * g * d⁻¹) (D.act d z) (D.j d * x) = D.kt k a g z x := by
  have hT : D.Te a (d * g * d⁻¹) (D.j d * x) = D.Te a g x :=
    Finset.sum_congr rfl fun i _ => congrArg D.ee (by simp only [map_mul, map_inv]; group)
  have hQ : qq k (D.act d z) (D.act (d * g * d⁻¹) (D.act d z)) * D.J k (d * g * d⁻¹) (D.act d z) =
      qq k z (D.act g z) * D.J k g z := by
    simp only [qq, Dat.J, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    change q1 (k v) (D.r v d • z v) (D.r v (d * g * d⁻¹) • D.r v d • z v) * j1 (k v) (D.r v (d * g * d⁻¹)) (D.r v d • z v) = _
    rw [smul_smul, ← map_mul, inv_mul_cancel_right, map_mul, mul_smul, map_mul, map_mul, map_inv]
    exact qj_conj (k v) (D.r v d) (D.r v g) (z v)
  unfold Dat.kt; rw [hT, hQ]

lemma kk_mk_jl [Fintype ι] (k : I → ℕ) (a : ι → Gf) (hH : D.Hyp k a) (g : GL2 F) (x : Gf) (z : X I) :
    D.kk k a (g : PG F) (((x : Gf ⧸ D.H) : D.Om), (z : D.Xs)) = D.kt k a g z x := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL2 F)) g
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul D.H x
  change D.kt k a (g : PG F).out z (Quotient.out (x : Gf ⧸ D.H)) = D.kt k a g z x
  rw [hc, hh, kt_mul_center_jl D k a hH.compat g c c.2, kt_mul_H_jl D k a hH.good]

lemma kk_conj [Fintype ι] (k : I → ℕ) (a : ι → Gf) (hH : D.Hyp k a) (δ γ : PG F) (y : D.Y) :
    D.kk k a (δ * γ * δ⁻¹) (δ • y) = D.kk k a γ y := by
  obtain ⟨y1, y2⟩ := y; obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective δ
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  obtain ⟨x, rfl⟩ : ∃ x : Gf, ((x : Gf ⧸ D.H) : D.Om) = y1 := QuotientGroup.mk_surjective y1
  rw [show (d : PG F) * g * (d : PG F)⁻¹ = ((d * g * d⁻¹ : GL2 F) : PG F) by simp,
    show (d : PG F) • ((((x : Gf ⧸ D.H) : D.Om),
                        y2) : D.Y) = ((((D.j d * x : Gf) : Gf ⧸ D.H) : D.Om), D.act d y2) from
      Prod.ext (D.mk_smulO d x) (D.mk_smulX d y2)]
  calc _ = D.kt k a (d * g * d⁻¹) (D.act d y2) (D.j d * x) := kk_mk_jl D k a hH _ _ _
    _ = D.kt k a g y2 x := kt_conj_jl D k a d g y2 x
    _ = _ := (kk_mk_jl D k a hH _ _ _).symm

lemma meas_kk [Fintype ι] (k : I → ℕ) (a : ι → Gf) (hH : D.Hyp k a) (γ : PG F) : Measurable (D.kk k a γ) := by
  have := hH.ax.cO
  refine measurable_from_prod_countable_right fun ω => ?_
  have hc : Continuous fun z : X I => qq k z (D.act γ.out z) * D.J k γ.out z :=
    (continuous_finsetProd _ fun v _ => (cont_q1 (k v)).comp ((continuous_apply v).prodMk
      ((cont_smul_P (D.r v γ.out)).comp (continuous_apply v)))).mul
      (continuous_finsetProd _ fun v _ => (cont_j1 (k v) (D.r v γ.out)).comp (continuous_apply v))
  show Measurable fun z : D.Xs => D.Te a γ.out (D.rep ω) * (qq k z (D.act γ.out z) * D.J k γ.out z)
  exact measurable_const.mul hc.measurable

lemma norm_kk_le [Fintype ι] (k : I → ℕ) (a : ι → Gf) (hH : D.Hyp k a) (γ : PG F) (y : D.Y) :
    ‖D.kk k a γ y‖ ≤ (Fintype.card ι * cst_jl k) * Kap k y.2 (γ • y.2 : D.Xs) := by
  rw [smulX_out_jl]; unfold Dat.kk Dat.kt; rw [norm_mul, mul_assoc]
  have hQJ : ‖qq k y.2 (D.act γ.out y.2) * D.J k γ.out y.2‖ = cst_jl k * Kap k y.2 (D.act γ.out y.2) := by
    simp only [qq, Dat.J, Dat.act, Kap, cst_jl, norm_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => norm_qj_jl (k v) (le_trans (by norm_num) (hH.four v)) (D.r v γ.out) (y.2 v)
  have h0 := norm_nonneg (qq k y.2 (D.act γ.out y.2) * D.J k γ.out y.2)
  rw [hQJ] at h0 ⊢; exact mul_le_mul_of_nonneg_right (norm_Te_le_jl D hH.ax a γ.out _) h0

omit [Fintype I] in
lemma kk_supp [Fintype ι] (a : ι → Gf) (γ : PG F) (y : D.Om) (hT : D.Te a γ.out (D.rep y) ≠ 0) :
    ∃ i, γ • y = ((D.rep y * a i : Gf) : Gf ⧸ D.H) := by
  obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hT
  have hm : (D.rep y)⁻¹ * (D.j γ.out)⁻¹ * D.rep y * a i ∈ D.H :=
      by by_contra hn; exact hi (by simp [Dat.ee, hn])
  exact ⟨i, by rw [smulO_out_jl]; exact QuotientGroup.eq.2 (by simpa [mul_assoc] using hm)⟩

lemma kk_reg [Fintype ι] (k : I → ℕ) (a : ι → Gf) (hH : D.Hyp k a) (γ : PG F) (y : D.Om) (i : ι)
    (hγ : γ • y = ((D.rep y * a i : Gf) : Gf ⧸ D.H)) :
    γ.out.val.trace ≠ 0 ∧ γ.out.val.trace ^ 2 ≠ 4 * γ.out.val.det := by
  rw [smulO_out_jl] at hγ
  exact hH.reg γ.out (D.rep y) i (by
    rw [show (a i)⁻¹ * ((D.rep y)⁻¹ * D.j γ.out * D.rep y) = ((D.j γ.out * D.rep y)⁻¹ * (D.rep y * a i))⁻¹ by group]
    exact D.H.inv_mem (QuotientGroup.eq.1 hγ))

-- === E0d: Heights on quotient ===

lemma htY_mk_jl (hA : D.Ax) (s : Fin 2 → F) (hs : s ≠ 0) (z : X I) (x : Gf) :
    D.HtY s ((((x : Gf ⧸ D.H) : D.Om), (z : D.Xs)) : D.Y) = D.Ht s z x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul D.H x
  simp only [Dat.HtY, Dat.Ht, Dat.rep]; rw [hh, hA.lev s hs x h h.2]

lemma htY_smul_jl (hA : D.Ax) (s : Fin 2 → F) (hs : s ≠ 0) (γ : GL2 F) (y : D.Y) :
    D.HtY s ((γ : PG F) • y) = D.HtY (s ᵥ* γ.val) y := by
  obtain ⟨ω, z⟩ := y
  obtain ⟨x, rfl⟩ : ∃ x : Gf, ((x : Gf ⧸ D.H) : D.Om) = ω := QuotientGroup.mk_surjective ω
  have e0 : (γ : PG F) • ((((x : Gf ⧸ D.H) : D.Om),
                           z) : D.Y) = ((((D.j γ * x : Gf) : Gf ⧸ D.H) : D.Om),
                                        (D.act γ z : D.Xs)) :=
    Prod.ext (D.mk_smulO γ x) (D.mk_smulX γ z)
  have h1 : D.HtY s ((γ : PG F) • ((((x : Gf ⧸ D.H) : D.Om),
                                    z) : D.Y)) = D.Ht s (D.act γ z) (D.j γ * x) :=
    (congrArg (D.HtY s) e0).trans (htY_mk_jl D hA s hs (D.act γ z) (D.j γ * x))
  have h2 : D.HtY (s ᵥ* γ.val) ((((x : Gf ⧸ D.H) : D.Om), z) : D.Y) = D.Ht (s ᵥ* γ.val) z x :=
    htY_mk_jl D hA _ (vecMul_ne_jl hs γ) z x
  rw [h1, h2]
  simp only [Dat.Ht, Dat.act, ← hA.rat s hs γ x]
  have key v : |(D.r v γ • z v).1.im| / ‖(D.σ v (s 0) : ℂ) * (D.r v γ • z v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2 =
      |D.σ v γ.val.det| * (|(z v).1.im| / ‖(D.σ v ((s ᵥ* γ.val) 0) : ℂ) * (z v).1 + (D.σ v ((s ᵥ* γ.val) 1) : ℂ)‖ ^ 2) := by
    have h0 := den_ne (D.r v γ) (z v).2
    have e : (D.σ v (s 0) : ℂ) * (D.r v γ • z v).1 + (D.σ v (s 1) : ℂ) =
        ((D.σ v ((s ᵥ* γ.val) 0) : ℂ) * (z v).1 + (D.σ v ((s ᵥ* γ.val) 1) : ℂ)) / den (D.r v γ) (z v).1 := by
      rw [coe_smul, eq_div_iff h0, add_mul, mul_assoc, div_mul_cancel₀ _ h0]
      simp only [num, den, vecMul, dotProduct, Fin.sum_univ_two, map_add, map_mul]
      change (D.σ v (s 0) : ℂ) * ((D.σ v (γ 0 0) : ℂ) * (z v).1 + D.σ v (γ 0 1)) +
          D.σ v (s 1) * ((D.σ v (γ 1 0) : ℂ) * (z v).1 + D.σ v (γ 1 1)) = _
      push_cast; ring
    have hn : 0 < ‖den (D.r v γ) (z v).1‖ ^ 2 := by positivity
    rw [e, im_smul_jl, r_det_jl, norm_div, div_pow, abs_div, abs_mul, normSq_eq_norm_sq,
      abs_of_nonneg hn.le, div_div_div_cancel_right₀ hn.ne', mul_div_assoc]
  rw [Finset.prod_congr rfl fun v _ => key v, Finset.prod_mul_distrib]; ring

lemma htY_smulc_jl (hA : D.Ax) (s : Fin 2 → F) (hs : s ≠ 0) (c : F) (hc : c ≠ 0) : D.HtY (c • s) = D.HtY s := by
  funext y; simp only [Dat.HtY, Dat.Ht, hA.smul s hs c hc]
  have key v : |(y.2 v).1.im| / ‖(D.σ v ((c • s) 0) : ℂ) * (y.2 v).1 + (D.σ v ((c • s) 1) : ℂ)‖ ^ 2 =
      (|(y.2 v).1.im| / ‖(D.σ v (s 0) : ℂ) * (y.2 v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2) / D.σ v c ^ 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, ofReal_mul]
    rw [show (D.σ v c : ℂ) * D.σ v (s 0) * (y.2 v).1 + D.σ v c * D.σ v (s 1) =
        D.σ v c * (D.σ v (s 0) * (y.2 v).1 + D.σ v (s 1)) by ring, norm_mul, norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs, div_div, mul_comm (D.σ v c ^ 2)]
  rw [Finset.prod_congr rfl fun v _ => key v, Finset.prod_div_distrib]
  have hp : ∏ v, D.σ v c ^ 2 ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero 2 ((map_ne_zero _).2 hc)
  field_simp

omit [Fintype I] in
lemma lin_ne_jl (s : Fin 2 → F) (hs : s ≠ 0) (v : I) (z : P) : (D.σ v (s 0) : ℂ) * z.1 + (D.σ v (s 1) : ℂ) ≠ 0 :=
    fun h => by
  have h1 := congrArg im h; have h2 := congrArg re h; simp at h1 h2
  have a0 : s 0 = 0 := h1.resolve_right z.2
  rw [a0, map_zero, zero_mul, zero_add] at h2
  exact hs $ funext fun i => by fin_cases i; exact a0; exact (map_eq_zero _).1 h2

lemma htY_pos_jl (hA : D.Ax) (s : Fin 2 → F) (hs : s ≠ 0) (y : D.Y) : 0 < D.HtY s y :=
  mul_pos (Finset.prod_pos fun v _ => div_pos (abs_pos.2 (y.2 v).2) (pow_pos (norm_pos_iff.2 (lin_ne_jl D s hs v _)) 2))
    (hA.pos s hs _)

lemma htY_prod_jl (hA : D.Ax) (s s' : Fin 2 → F) (hd : s 0 * s' 1 - s 1 * s' 0 ≠ 0) (y : D.Y) :
    D.HtY s y * D.HtY s' y ≤ 1 := by
  have hs : s ≠ 0 := by rintro rfl; simp at hd
  have hs' : s' ≠ 0 := by rintro rfl; simp at hd
  have hl v : |(y.2 v).1.im| / ‖(D.σ v (s 0) : ℂ) * (y.2 v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2 *
      (|(y.2 v).1.im| / ‖(D.σ v (s' 0) : ℂ) * (y.2 v).1 + (D.σ v (s' 1) : ℂ)‖ ^ 2) *
      D.σ v (s 0 * s' 1 - s 1 * s' 0) ^ 2 ≤ 1 := by
    set a := D.σ v (s 0); set b :=
        D.σ v (s 1); set a' := D.σ v (s' 0); set b' := D.σ v (s' 1); set z := y.2 v
    have hw :=
        norm_pos_iff.2 (lin_ne_jl D s hs v z); have hw' := norm_pos_iff.2 (lin_ne_jl D s' hs' v z)
    have hkey : |z.1.im| * |a * b' - b * a'| ≤ ‖(a : ℂ) * z.1 + b‖ * ‖(a' : ℂ) * z.1 + b'‖ := by
      have e : (((a : ℂ) * z.1 + b) * conj ((a' : ℂ) * z.1 + b')).im = (a * b' - b * a') * z.1.im :=
          by simp; ring
      calc _ = |(((a : ℂ) * z.1 + b) * conj ((a' : ℂ) * z.1 + b')).im| := by rw [e, abs_mul,
                                                                                 mul_comm]
        _ ≤ _ := (abs_im_le_norm _).trans_eq (by rw [norm_mul, norm_conj])
    rw [map_sub, map_mul, map_mul, ← sq_abs (a * b' - b * a'), div_mul_div_comm, div_mul_eq_mul_div,
        div_le_one (by positivity)]
    nlinarith [pow_le_pow_left₀ (by positivity) hkey 2]
  simp only [Dat.HtY, Dat.Ht]
  calc _ = ((∏ v, |(y.2 v).1.im| / ‖(D.σ v (s 0) : ℂ) * (y.2 v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2) *
          (∏ v, |(y.2 v).1.im| / ‖(D.σ v (s' 0) : ℂ) * (y.2 v).1 + (D.σ v (s' 1) : ℂ)‖ ^ 2)) *
          (D.hf s (D.rep y.1) * D.hf s' (D.rep y.1)) := by ring
    _ ≤ _ * ∏ v, D.σ v (s 0 * s' 1 - s 1 * s' 0) ^ 2 :=
        mul_le_mul_of_nonneg_left (hA.prod s s' hd _) (by positivity)
    _ = ∏ v, _ := by rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    _ ≤ 1 := Finset.prod_le_one₀ (fun _ _ => by positivity) fun v _ => hl v

lemma meas_htY_jl (hA : D.Ax) (s : Fin 2 → F) : Measurable (D.HtY s) := by
  have := hA.cO
  refine measurable_from_prod_countable_right fun ω => ?_
  have hp : Measurable fun z : D.Xs => ∏ v, |(z v).1.im| / ‖(D.σ v (s 0) : ℂ) * (z v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2 :=
    Finset.measurable_prod _ fun v _ => by
      have hz : Measurable fun z : D.Xs => (z v).1 :=
          measurable_subtype_coe.comp (measurable_pi_apply v)
      have h1 : Measurable fun z : D.Xs => |(z v).1.im| :=
          continuous_abs.measurable.comp (measurable_im.comp hz)
      have h2 : Measurable fun z : D.Xs => ‖(D.σ v (s 0) : ℂ) * (z v).1 + (D.σ v (s 1) : ℂ)‖ ^ 2 :=
        ((measurable_const.mul hz).add measurable_const).norm.pow_const 2
      exact h1.div h2
  exact hp.mul_const (D.hf s (D.rep ω))

lemma meas_lam_jl (hA : D.Ax) (T : ℝ) : MeasurableSet (D.abelian₂ T) := by
  have := hA.cF
  rw [show D.abelian₂ T = ⋂ s : Fin 2 → F, ⋂ (_ : s ≠ 0),
      {y | D.HtY s y ≤ T} from Set.ext fun _ => by simp [Dat.abelian₂]]
  exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ => measurableSet_le (meas_htY_jl D hA s) measurable_const

lemma lam_smul_jl (hA : D.Ax) (T : ℝ) (δ : PG F) (y : D.Y) (h : y ∈ D.abelian₂ T) : δ • y ∈ D.abelian₂ T := by
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective δ
  intro s hs; rw [htY_smul_jl D hA s hs]; exact h _ (vecMul_ne_jl hs d)

lemma meas_lamF_jl (hA : D.Ax) (T : ℝ) (γ : PG F) : MeasurableSet (D.LamF T γ) := by
  have := hA.cF
  rw [show D.LamF T γ = ⋂ s : Fin 2 → F, ⋂ (_ : s ≠ 0), ⋂ (_ : Fix s γ),
      {y | D.HtY s y ≤ T} from Set.ext fun _ => by simp [Dat.LamF]]
  exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    measurableSet_le (meas_htY_jl D hA s) measurable_const

lemma lamF_smul_jl (hA : D.Ax) (T : ℝ) (γ δ : PG F) (y : D.Y) (h : y ∈ D.LamF T γ) :
    δ • y ∈ D.LamF T (δ * γ * δ⁻¹) := by
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective δ; obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  intro s hs hf; rw [htY_smul_jl D hA s hs]; exact h _ (vecMul_ne_jl hs d) ((fix_mk_jl _ g).2 ((fix_conj_jl s g d).1 hf))

lemma htY_bdd (hA : D.Ax) (y : D.Y) : ∃ T₀, ∀ T, T₀ ≤ T → y ∈ D.abelian₂ T := by
  by_cases h : ∃ s0 : Fin 2 → F, s0 ≠ 0 ∧ 1 < D.HtY s0 y
  · obtain ⟨s0, h0, h1⟩ := h
    refine ⟨max 1 (D.HtY s0 y), fun T hT s hs => ?_⟩
    by_cases h2 : D.HtY s y ≤ 1
    · exact h2.trans ((le_max_left _ _).trans hT)
    · push Not at h2
      by_cases hd : s0 0 * s 1 - s0 1 * s 0 = 0
      · have hline : ∃ c : F, c ≠ 0 ∧ s = c • s0 := by
          by_cases a : s0 0 = 0
          · have b : s0 1 ≠ 0 := fun b => h0 (funext fun i => by fin_cases i <;> simp [a, b])
            have hs0 : s 0 = 0 :=
                (mul_eq_zero.1 (by linear_combination -hd + a * s 1)).resolve_left b
            refine ⟨s 1 / s0 1, fun hc => hs (funext fun i => by fin_cases i <;> simp [hs0,
                                                                                       (div_eq_zero_iff.1 hc).resolve_right b]),
              funext fun i => by fin_cases i <;> simp [hs0, a, b]⟩
          · refine ⟨s 0 / s0 0, fun hc => hs (funext fun i => by
                have e0 := (div_eq_zero_iff.1 hc).resolve_right a
                have e1 :=
                    (mul_eq_zero.1 (show s0 0 * s 1 = 0 by linear_combination hd + s0 1 * e0)).resolve_left a
                fin_cases i <;> simp [e0, e1]),
              funext fun i => by fin_cases i; simp [a]; simp only [Fin.mk_one, Fin.isValue,
                                                                   Pi.smul_apply, smul_eq_mul]; field_simp; linear_combination hd⟩
        obtain ⟨c, hc,
                rfl⟩ := hline; rw [htY_smulc_jl D hA s0 h0 c hc]; exact (le_max_right _ _).trans hT
      · exfalso; nlinarith [htY_prod_jl D hA s0 s hd y]
  · push Not at h; exact ⟨1, fun T hT s hs => (h s hs).trans hT⟩

end DatLemmas

theorem kernel_terms_invariant_bounded_proof_jl : B1a → B1b → KernelTermsInvariantBounded :=
  fun _ _ _ _ _ _ _ _ _ _ D k a hH =>
    ⟨fun γ z x => kk_mk_jl D k a hH γ x z, kk_conj D k a hH, meas_kk D k a hH,
     ⟨_, norm_kk_le D k a hH⟩, kk_supp D a, kk_reg D k a hH⟩

theorem heights_on_quotient_proof_jl : B1a → E0d := fun _ _ _ _ _ _ _ D hA =>
  ⟨htY_mk_jl D hA, htY_smul_jl D hA, htY_smulc_jl D hA, htY_pos_jl D hA, htY_prod_jl D hA,
   meas_htY_jl D hA,
   fun T => ⟨meas_lam_jl D hA T,
             fun δ y => ⟨fun h => by simpa [inv_smul_smul] using lam_smul_jl D hA T δ⁻¹ _ h,
                         lam_smul_jl D hA T δ y⟩⟩,
   fun T γ => ⟨meas_lamF_jl D hA T γ, fun δ y => ⟨fun h => by
     have := lamF_smul_jl D hA T _ δ⁻¹ _ h; rwa [inv_smul_smul,
                                                 show δ⁻¹ * (δ * γ * δ⁻¹) * δ⁻¹⁻¹ = γ by group] at this, lamF_smul_jl D hA T γ δ y⟩⟩,
   htY_bdd D hA, row_exists, fix_conj_jl⟩

-- === KapInt & KapSum & E2 ===

lemma lint_prod_jl {I : Type} [Fintype I] [SigmaFinite (volume : Measure P)]
    (f : I → P → ℝ) (hf0 : ∀ v x, 0 ≤ f v x) (hm : ∀ v, Measurable (f v))
    (C : I → ℝ≥0) (hC : ∀ v, ∫⁻ x, oR (f v x) ≤ C v) :
    ∫⁻ w : I → P, oR (∏ v, f v (w v)) ≤ ((∏ v, C v : ℝ≥0) : ℝ≥0∞) := by
  have hint v : Integrable (f v) := ⟨(hm v).aestronglyMeasurable, by
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hf0 v))]; exact (hC v).trans_lt ENNReal.coe_lt_top⟩
  have hP : Integrable (fun w : I → P => ∏ v,
                        f v (w v)) := by rw [volume_pi]; exact Integrable.fintype_prod hint
  rw [← ofReal_integral_eq_lintegral_ofReal hP (ae_of_all _ fun w => Finset.prod_nonneg fun v _ => hf0 v _),
    integral_fintype_prod_volume_eq_prod, ENNReal.ofReal_prod_of_nonneg (fun v _ => integral_nonneg (hf0 v)), ENNReal.ofNNReal_finsetProd]
  exact Finset.prod_le_prod fun v _ => by rw [ofReal_integral_eq_lintegral_ofReal (hint v) (ae_of_all _ (hf0 v))]; exact hC v

theorem pf_KapInt_jl : B1a → B1b → B1c → B6 → KapInt := by
  intro hA _ _ h6 I _ k hk
  have : SigmaFinite (volume : Measure P) := hA.1
  choose Cv hCv using fun v => h6 (k v) (hk v)
  have hA' : ((∏ v, toNNReal ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) : ℝ≥0) : ℝ) =
      ∏ v, (8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [NNReal.coe_prod]; exact Finset.prod_congr rfl fun v _ => coe_toNNReal _ (by positivity)
  have har1 (z w w' : P) (h : 1 / 2 ≤ kap w w') (e : ℝ) (he : 0 ≤ e) : kap z w ^ e ≤ (8 : ℝ) ^ e * kap z w' ^ e := by
    rw [← mul_rpow (by norm_num) (kap_nonneg_jl _ _)]
    exact rpow_le_rpow (kap_nonneg_jl _ _) (by nlinarith [kap_tri z w w',
                                                          mul_le_mul_of_nonneg_left h (kap_nonneg_jl z w)]) he
  have har2 (z w w' : P) (h : 1 / 2 ≤ kap w w') : (|z.1.im| / |w.1.im|) ^ ((1 : ℝ) / 2) ≤ (8 : ℝ) ^ ((1 : ℝ) / 2) * (|z.1.im| / |w'.1.im|) ^ ((1 : ℝ) / 2) := by
    have hw := abs_pos.2 w.2; have hw' := abs_pos.2 w'.2
    rw [← mul_rpow (by norm_num) (div_nonneg (abs_nonneg _) hw'.le)]
    refine rpow_le_rpow (div_nonneg (abs_nonneg _) hw.le) ?_ (by norm_num)
    rw [mul_div_assoc', div_le_div_iff₀ hw hw']
    nlinarith [mul_le_mul_of_nonneg_left (show |w'.1.im| ≤ 8 * |w.1.im| by nlinarith [kap_im_le w w', mul_le_mul_of_nonneg_right h hw'.le]) (abs_nonneg z.1.im)]
  refine ⟨∏ v, Cv v, ∏ v, toNNReal ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)),
          fun z => ?_⟩
  have hkm v : Measurable (kap (z v)) :=
      (cont_kap.comp (continuous_const.prodMk continuous_id)).measurable
  have hm2 v : Measurable fun w : P => kap (z v) w ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |w.1.im|) ^ ((1 : ℝ) / 2) := by
    have hi : Measurable fun w : P => |w.1.im| :=
        continuous_abs.measurable.comp (measurable_im.comp measurable_subtype_coe)
    exact ((hkm v).pow_const _).mul ((measurable_const.div hi).pow_const _)
  have hsplit (w : X I) : Kap k z w * ∏ v, (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2) =
      ∏ v, (kap (z v) (w v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)) :=
    (Finset.prod_mul_distrib).symm
  refine ⟨Finset.measurable_prod _ fun v _ => ((hkm v).comp (measurable_pi_apply v)).pow_const _,
    lint_prod_jl (fun v w => kap (z v) w ^ ((k v : ℝ) / 2)) (fun _ _ => rpow_nonneg (kap_nonneg_jl _ _) _)
      (fun v => (hkm v).pow_const _) Cv fun v => (hCv v (z v)).1,
    by simp only [hsplit]; exact lint_prod_jl (fun v w => kap (z v) w ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |w.1.im|) ^ ((1 : ℝ) / 2))
        (fun v w => mul_nonneg (rpow_nonneg (kap_nonneg_jl _ _) _) (rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _))
        hm2 Cv fun v => (hCv v (z v)).2,
    fun w w' hn => ⟨?_, ?_⟩⟩
  · simp only [Kap]; rw [hA', ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ => rpow_nonneg (kap_nonneg_jl _ _) _) fun v _ => ?_
    have h8 : (1 : ℝ) ≤ (8 : ℝ) ^ ((1 : ℝ) / 2) := one_le_rpow (by norm_num) (by norm_num)
    have e1 := har1 (z v) (w v) (w' v) (hn v) ((k v : ℝ) / 2) (by positivity)
    have hp : 0 ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) :=
      mul_nonneg (by positivity) (rpow_nonneg (kap_nonneg_jl _ _) _)
    nlinarith [mul_le_mul_of_nonneg_left h8 hp]
  · rw [hsplit w, hsplit w', hA', ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ => mul_nonneg (rpow_nonneg (kap_nonneg_jl _ _) _) (by positivity)) fun v _ => ?_
    have e1 := har1 (z v) (w v) (w' v) (hn v) ((k v : ℝ) / 2) (by positivity)
    have e2 := har2 (z v) (w v) (w' v) (hn v)
    calc _ ≤ _ * _ :=
        mul_le_mul e1 e2 (by positivity) (mul_nonneg (by positivity) (rpow_nonneg (kap_nonneg_jl _ _) _))
      _ = _ := by ring

theorem pf_KapSum_jl : Pack → Mult → KapInt → KapSum := by
  intro hPack hMult hKap F I Gf _ _ _ D hD k hk c₀ hc₀
  obtain ⟨C₁, hC₁⟩ := hPack F I Gf D hD; obtain ⟨C₃, A₃, hK⟩ := hKap I k hk
  obtain ⟨C₂, hC₂⟩ := hMult F I Gf D hD (1 / 16) c₀ (by norm_num) hc₀
  refine ⟨(C₁ : ℝ) * A₃ * max C₂ 0 * C₃, fun y s hs hy ω' z => ?_⟩
  obtain ⟨hfin, hcard⟩ := hC₂ y s hs hy; obtain ⟨hmeas, hint, -, hnear⟩ := hK z
  have hcard' : (({γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)}.ncard : ℕ) : ℝ≥0∞) ≤
      oR (max C₂ 0 * (1 + D.HtY s y)) := by
    rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (hcard.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)))
  have hA (w w' : D.Xs) (hww : Near (1 / 2) w w') : oR (Kap k z w) ≤ (A₃ : ℝ≥0∞) * oR (Kap k z w') :=
    (ENNReal.ofReal_le_ofReal (hnear w w' hww).1).trans_eq
      ((ENNReal.ofReal_mul A₃.2).trans (congrArg (· * oR (Kap k z w')) ENNReal.ofReal_coe_nnreal))
  refine (hC₁ y ω' (fun w => oR (Kap k z w)) A₃ (ENNReal.measurable_ofReal.comp hmeas) hA hfin).trans ?_
  calc _ ≤ (C₁ : ℝ≥0∞) * A₃ * oR (max C₂ 0 * (1 + D.HtY s y)) * C₃ := by gcongr; exact hint
    _ = _ := by rw [show (C₁ : ℝ) * A₃ * max C₂ 0 * C₃ * (1 + D.HtY s y) =
          ((C₁ * A₃ * C₃ : ℝ≥0) : ℝ) * (max C₂ 0 * (1 + D.HtY s y)) by push_cast; ring,
        ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]; push_cast; ring

theorem kernel_sum_bounded_proof_jl : KernelTermsInvariantBounded → E0d → KapSum → E2 := by
  intro _ _ hks F I Gf ι _ _ _ _ D k a hyp
  obtain ⟨c₀, hc₀, hmink⟩ := hyp.ax.mink
  obtain ⟨C, hC⟩ := hks F I Gf D hyp.ax k hyp.four c₀ hc₀
  set C₀ : ℝ := Fintype.card ι * cst_jl k
  have key T (y : D.Y) (hy : y ∈ D.abelian₂ T) :
      ∑' γ : PG F, ‖D.kk k a γ y‖ₑ ≤ Fintype.card ι * (oR C₀ * oR (max C 0 * (1 + T))) := by
    obtain ⟨s, hs, hcs⟩ := hmink y.2 (D.rep y.1)
    have hcs' : c₀ ≤ D.HtY s y := hcs
    have hle : D.HtY s y ≤ T := hy s hs
    let S i := {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
    let g (γ : PG F) := oR C₀ * oR (Kap k y.2 (γ • y.2 : D.Xs))
    have hpt γ : ‖D.kk k a γ y‖ₑ ≤ ∑ i, (S i).indicator g γ := by
      by_cases h0 : D.Te a γ.out (D.rep y.1) = 0
      · simp [Dat.kk, Dat.kt, h0]
      · obtain ⟨i, hi⟩ := kk_supp D a γ y.1 h0
        refine le_trans ?_ (Finset.single_le_sum (f := fun j => (S j).indicator g γ) (fun _ _ => zero_le) (Finset.mem_univ i))
        rw [indicator_of_mem (show γ ∈ S i from hi)]
        exact (ofReal_norm _).symm.trans_le
          ((ENNReal.ofReal_le_ofReal (norm_kk_le D k a hyp γ y)).trans_eq (ENNReal.ofReal_mul' (Kap_nonneg_jl k _ _)))
    calc _ ≤ ∑' γ, ∑ i, (S i).indicator g γ := ENNReal.tsum_le_tsum hpt
      _ = ∑ i, ∑' γ, (S i).indicator g γ := Summable.tsum_finsetSum fun _ _ => ENNReal.summable
      _ ≤ ∑ _i : ι, oR C₀ * oR (max C 0 * (1 + T)) := Finset.sum_le_sum fun i _ => by
            rw [← _root_.tsum_subtype, ENNReal.tsum_mul_left]; gcongr
            exact (hC y s hs hcs' _ y.2).trans (ENNReal.ofReal_le_ofReal (mul_le_mul (le_max_left _ _) (by linarith) (by linarith) (le_max_right _ _)))
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ⟨fun y => ?_, fun T => ⟨Fintype.card ι * (C₀.toNNReal * (max C 0 * (1 + T)).toNNReal),
                                 fun y hy => ?_⟩⟩
  · obtain ⟨T₀, hT₀⟩ := htY_bdd D hyp.ax y
    have hnt : (Fintype.card ι : ℝ≥0∞) * (oR C₀ * oR (max C 0 * (1 + T₀))) ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    exact (ENNReal.summable_toReal (ne_top_of_le_ne_top hnt (key T₀ y (hT₀ T₀ le_rfl)))).congr fun _ => toReal_enorm _
  · exact (key T y hy).trans (le_of_eq (by simp [oR, ENNReal.ofReal]))

-- === C2: Orbit cover & partition of unity ===

lemma exists_cut_jl {G Y : Type} [Group G] [Countable G] [MeasurableSpace Y] [MulAction G Y]
    (hm : ∀ g : G, Measurable fun y : Y => g • y) (u : Y → ℝ) (hu : Measurable u)
    (h0 : ∀ y, 0 ≤ u y) (hpos : ∀ y, ∃ g : G, 0 < u (g • y)) (hs : ∀ y,
                                                              Summable fun g : G => u (g • y)) :
    ∃ b : Y → ℝ, IsCut G b := by
  have hsm : Measurable fun y => ∑' g : G, u (g • y) := by
    rw [show (fun y => ∑' g : G, u (g • y)) = fun y => (∑' g : G,
                                                        oR (u (g • y))).toReal from funext fun y => by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => h0 _) (hs y),
          ENNReal.toReal_ofReal (tsum_nonneg fun _ => h0 _)]]
    exact (Measurable.tsum fun g => (hu.comp (hm g)).ennreal_ofReal).ennreal_toReal
  have hspos y : 0 < ∑' g : G, u (g • y) := let ⟨g,
                                                 hg⟩ := hpos y; hg.trans_le ((hs y).le_tsum g fun _ _ => h0 _)
  refine ⟨fun y => u y / ∑' g : G, u (g • y), hu.div hsm, fun y => div_nonneg (h0 y) (hspos y).le,
          fun y => ?_⟩
  have e : (fun g : G => u (g • y) / ∑' h : G,
            u (h • g • y)) = fun g => u (g • y) / ∑' h : G, u (h • y) :=
    funext fun g => congrArg (u (g • y) / ·) (by simp only [smul_smul]; exact (Equiv.mulRight g).tsum_eq fun h => u (h • y))
  show HasSum _ 1; rw [e, ← div_self (hspos y).ne']; exact (hs y).hasSum.div_const _

lemma orbit_cover {G Y : Type} [Group G] [Countable G] [MeasurableSpace Y] [MulAction G Y]
    (μ : Measure Y) (hP : Pres G μ) (b : Y → ℝ) (hb : IsCut G b) (S : Set Y)
    (hS : MeasurableSet S) (hc : ∀ y : Y, ∃ g : G, g • y ∈ S) : ∫⁻ y, oR (b y) ∂μ ≤ μ S := by
  have hF (g : G) : Measurable (S.indicator fun y => oR (b (g⁻¹ • y))) :=
    (hb.meas.ennreal_ofReal.comp (hP g⁻¹).measurable).indicator hS
  have hone y : ∑' g : G, oR (b (g⁻¹ • y)) = 1 := by
    rw [show (∑' g : G, oR (b (g⁻¹ • y))) = ∑' g : G,
        oR (b (g • y)) from (Equiv.inv G).tsum_eq (fun g : G => oR (b (g • y))),
      ← ENNReal.ofReal_tsum_of_nonneg (fun _ => hb.nonneg _) (hb.sum y).summable, (hb.sum y).tsum_eq, ENNReal.ofReal_one]
  calc ∫⁻ y, oR (b y) ∂μ ≤ ∫⁻ y, ∑' g : G, S.indicator (fun y => oR (b (g⁻¹ • y))) (g • y) ∂μ :=
        lintegral_mono fun y => let ⟨g, hg⟩ := hc y; le_trans (by rw [indicator_of_mem hg,
                                                                      inv_smul_smul]) (ENNReal.le_tsum g)
    _ = ∑' g : G, ∫⁻ y, S.indicator (fun y => oR (b (g⁻¹ • y))) (g • y) ∂μ :=
        lintegral_tsum fun g => ((hF g).comp (hP g).measurable).aemeasurable
    _ = ∑' g : G, ∫⁻ y, S.indicator (fun y => oR (b (g⁻¹ • y))) y ∂μ :=
        tsum_congr fun g => (hP g).lintegral_comp (hF g)
    _ = ∫⁻ y, ∑' g : G, S.indicator (fun y => oR (b (g⁻¹ • y))) y ∂μ :=
        (lintegral_tsum fun g => (hF g).aemeasurable).symm
    _ = ∫⁻ y, S.indicator 1 y ∂μ :=
        lintegral_congr fun y => by by_cases hy : y ∈ S <;> simp [indicator, hy, hone]
    _ = μ S := lintegral_indicator_one hS

theorem orbit_cover_proof_jl : C2 := fun _ _ _ _ _ _ => ⟨exists_cut_jl, orbit_cover⟩

-- === Ecut ===

theorem pf_Ecut_jl : B1b → B1c → C2 → E0a → E0d → KapSum → Ecut := by
  intro _ _ _ hE _ hK F I Gf _ _ _ D hax
  obtain ⟨hcount, -, hpres, -⟩ := hE F I Gf D hax
  have : Countable (PG F) := hcount; have : Countable D.Om := hax.cO
  obtain ⟨c₀, hc₀, hmk⟩ := hax.mink
  obtain ⟨C, hCK⟩ := hK F I Gf D hax (fun _ => 4) (fun _ => le_rfl) c₀ hc₀
  let iN : P := ⟨-Complex.I, by simp⟩
  let bs (e : I → Bool) : X I := fun v => if e v then iP else iN
  let uX (z : X I) : ℝ := ∑ e : I → Bool, Kap (fun _ => 4) (bs e) z
  have hu0 z : 0 ≤ uX z := Finset.sum_nonneg fun _ _ => Kap_nonneg_jl _ _ _
  have hupos z : 0 < uX z := Finset.sum_pos' (fun _ _ => Kap_nonneg_jl _ _ _)
    ⟨fun v => decide (0 < (z v).1.im), Finset.mem_univ _,
     Finset.prod_pos fun v _ => rpow_pos_of_pos (by
      unfold kap bs; by_cases h : 0 < (z v).1.im
      · simp only [h, decide_true, ↓reduceIte, iP]; rw [ite_eq_left (by simpa using h)]
        exact div_pos (by simp; linarith) (pos_den_conj (by simpa using h))
      · have h' : (z v).1.im < 0 := lt_of_le_of_ne (not_lt.1 h) (z v).2
        simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte,
                   iN]; rw [ite_eq_left (by simp; linarith)]
        exact div_pos (by simp; linarith) (pos_den_conj (by simp; linarith))) _⟩
  have hucont : Continuous uX :=
      continuous_finsetSum _ fun _ _ => continuous_finsetProd _ fun v _ =>
    (cont_kap.comp (continuous_const.prodMk (continuous_apply v))).rpow_const fun _ => Or.inr (by positivity)
  have hsplit z : oR (uX z) = ∑ e : I → Bool, oR (Kap (fun _ => 4) (bs e) z) :=
    ENNReal.ofReal_sum_of_nonneg fun _ _ => Kap_nonneg_jl _ _ _
  have hfib (y : D.Y) : ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ (e : I → Bool) (ω' : D.Om),
      ∑' γ : {γ : PG F // γ • y.1 = ω'}, oR (Kap (fun _ => 4) (bs e) (γ.1 • y.2 : D.Xs)) ≤ M :=
    let ⟨s, hs, hsy⟩ := hmk y.2 (D.rep y.1); ⟨_, ENNReal.ofReal_ne_top,
                                              fun e ω' => hCK y s hs hsy ω' (bs e)⟩
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat D.Om
  let w (ω : D.Om) : ℝ := (1 / 2 : ℝ) ^ f ω
  have hW : ∑' ω, oR (w ω) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' n : ℕ, (1 / 2 : ℝ) ^ n)) $
      (ENNReal.tsum_comp_le_tsum_of_injective hf fun n => oR ((1 / 2 : ℝ) ^ n)).trans_eq
        (ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) summable_geometric_two).symm
  have hm1 : Measurable fun y : D.Y => w y.1 :=
      (Measurable.of_discrete (f := w)).comp measurable_fst
  have hm2 : Measurable fun y : D.Y => uX y.2 := hucont.measurable.comp measurable_snd
  refine ⟨exists_cut_jl (fun g => (Measurable.of_discrete.comp measurable_fst).prodMk ((hpres g).measurable.comp measurable_snd))
      (fun y => w y.1 * uX y.2) (hm1.mul hm2)
      (fun y => mul_nonneg (by positivity) (hu0 _))
      (fun y => ⟨1,
                 by simpa using mul_pos (by positivity : (0 : ℝ) < w y.1) (hupos y.2)⟩) fun y => ?_,
    fun ω S hS => exists_cut_jl (fun g : S => (hpres (g : PG F)).measurable) uX hucont.measurable hu0
      (fun z => ⟨1, by simpa using hupos z⟩) fun z => ?_⟩
  · obtain ⟨M, hM, hMb⟩ := hfib y
    have hle : ∑' g : PG F, oR (w (g • y).1 * uX (g • y).2) ≤ ∑ _e : I → Bool, (∑' ω,
                                                                                oR (w ω)) * M := by
      calc _ = ∑' g : PG F, ∑ e : I → Bool, oR (w (g • y.1)) * oR (Kap (fun _ => 4) (bs e) (g • y.2 : D.Xs)) :=
              tsum_congr fun g => (ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ w (g • y.1))).trans
                ((congrArg (oR (w (g • y.1)) * ·) (hsplit (g • y.2 : X I))).trans (Finset.mul_sum _ _ _))
        _ = ∑ e : I → Bool, ∑' g : PG F, oR (w (g • y.1)) * oR (Kap (fun _ => 4) (bs e) (g • y.2 : D.Xs)) :=
              Summable.tsum_finsetSum fun _ _ => ENNReal.summable
        _ ≤ _ := Finset.sum_le_sum fun e _ => by
              rw [← ENNReal.tsum_fiberwise _ (fun g : PG F => g • y.1), ← ENNReal.tsum_mul_right]
              exact ENNReal.tsum_le_tsum fun ω' => by
                rw [show (∑' b : (fun g : PG F => g • y.1) ⁻¹' {ω'},
                          oR (w (b.1 • y.1)) * oR (Kap (fun _ => 4) (bs e) (b.1 • y.2 : D.Xs)))
                  = oR (w ω') * ∑' b : {g : PG F // g • y.1 = ω'}, oR (Kap (fun _ => 4) (bs e) (b.1 • y.2 : D.Xs)) by
                    rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun b => by rw [show b.1 • y.1 = ω' from b.2]]
                gcongr; exact hMb e ω'
    exact (ENNReal.summable_toReal (ne_top_of_le_ne_top (ENNReal.sum_lt_top.2 fun _ _ => ENNReal.mul_lt_top hW.lt_top hM.lt_top).ne hle)).congr
      fun _ => ENNReal.toReal_ofReal (mul_nonneg (by positivity) (hu0 _))
  · obtain ⟨M, hM, hMb⟩ := hfib ((ω, z) : D.Y)
    have hinj : Injective (fun g : S => (⟨(g : PG F), hS g.2⟩ : {γ : PG F // γ • ((ω,
                                                                                   z) : D.Y).1 = ω})) :=
      fun _ _ h => Subtype.ext (congrArg (fun x : {γ : PG F // γ • ((ω, z) : D.Y).1 = ω} => x.1) h)
    have hle : ∑' g : S, oR (uX (g • z : D.Xs)) ≤ ∑ _e : I → Bool, M := by
      calc _ = ∑' g : S, ∑ e : I → Bool, oR (Kap (fun _ => 4) (bs e) (g • z : D.Xs)) :=
          tsum_congr fun _ => hsplit _
        _ = ∑ e : I → Bool, ∑' g : S, oR (Kap (fun _ => 4) (bs e) (g • z : D.Xs)) :=
            Summable.tsum_finsetSum fun _ _ => ENNReal.summable
        _ ≤ _ := Finset.sum_le_sum fun e _ => (ENNReal.tsum_comp_le_tsum_of_injective hinj
            fun γ => oR (Kap (fun _ => 4) (bs e) (γ.1 • z : D.Xs))).trans (hMb e ω)
    exact (ENNReal.summable_toReal (ne_top_of_le_ne_top (ENNReal.sum_lt_top.2 fun _ _ => hM.lt_top).ne hle)).congr
      fun _ => ENNReal.toReal_ofReal (hu0 _)

end UpperTheory.Esk

-- ==== B2

noncomputable section

open MeasureTheory Matrix Finset Filter Function Subgroup MulAction QuotientGroup Topology Metric
open Set hiding center
open Real hiding dist_eq
open _root_.Complex hiding log exp exp_add exp_neg exp_log exp_nat_mul log_mul log_exp exp_sub
open scoped ENNReal NNReal ComplexConjugate Classical Real

namespace UpperTheory.Esk

-- === Reusable measurable equivalences & ext1 helpers ===

def actEquiv_jl {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] {μ : Measure Y}
    (hP : Pres G μ) (g : G) : Y ≃ᵐ Y where
  toEquiv := MulAction.toPerm g
  measurable_toFun := (hP g).measurable
  measurable_invFun := (hP g⁻¹).measurable

lemma ext1_coe (f : P → ℂ) (z : P) : ext1 f z.1 = f z := by unfold ext1; rw [dite_eq_left z.2]; rfl

lemma ext1_of_im (f : P → ℂ) {t : ℂ} (h : t.im ≠ 0) : ext1 f t = f ⟨t,
                                                                    h⟩ := by unfold ext1; rw [dite_eq_left h]

-- === FormsStableUnderOperators ===

lemma hol1_finset_sum {ι : Type} (s : Finset ι) (g : ι → P → ℂ) (h : ∀ i ∈ s, Hol1 (g i)) :
    Hol1 (fun t => ∑ i ∈ s, g i t) := by
  have e : ext1 (fun t => ∑ i ∈ s,
                 g i t) = fun t => ∑ i ∈ s, ext1 (g i) t := funext fun t => by unfold ext1; split_ifs <;> simp
  unfold Hol1; rw [e]; exact (DifferentiableOn.sum h).congr fun _ _ => by simp [Finset.sum_apply]

lemma hol1_add {f g : P → ℂ} (hf : Hol1 f) (hg : Hol1 g) : Hol1 (fun t => f t + g t) := by
  have e : ext1 (fun t => f t + g t) = fun t => ext1 f t + ext1 g t :=
      funext fun t => by unfold ext1; split_ifs <;> simp
  unfold Hol1 at *; rw [e]; exact hf.add hg

lemma hol1_const_mul (c : ℂ) {f : P → ℂ} (hf : Hol1 f) : Hol1 (fun t => c * f t) := by
  have e : ext1 (fun t => c * f t) = fun t => c * ext1 f t :=
      funext fun t => by unfold ext1; split_ifs <;> simp
  unfold Hol1 at *; rw [e]; exact hf.const_mul c

lemma hol1_zero : Hol1 (fun _ : P => (0 : ℂ)) := by
  have e : ext1 (fun _ : P => (0 : ℂ)) = fun _ => 0 :=
      funext fun t => by unfold ext1; split_ifs <;> simp
  unfold Hol1; rw [e]; exact differentiableOn_const 0

lemma isForm_sub {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf) (k : I → ℕ) :
    ∀ f, f ∈ D.M k ↔ D.IsForm k f := by
  let S : Submodule ℂ (X I × Gf → ℂ) :=
    { carrier := {f | D.IsForm k f}
      zero_mem' := ⟨fun _ => ⟨continuous_const, fun _ _ => hol1_zero⟩, fun _ _ _ => by simp,
                    fun _ _ _ => by simp, ⟨0, fun _ _ => by simp⟩⟩
      add_mem' := fun {f g} hf hg => ⟨fun x => ⟨(hf.hol x).1.add (hg.hol x).1,
                                                fun z v => hol1_add ((hf.hol x).2 z v) ((hg.hol x).2 z v)⟩,
        fun γ z x => by simp [hf.aut, hg.aut, mul_add], fun z x h => by simp [hf.lev, hg.lev,
                                                                              mul_add],
        let ⟨C₁, h₁⟩ := hf.bdd; let ⟨C₂, h₂⟩ := hg.bdd
        ⟨C₁ + C₂,
         fun z x => (mul_le_mul_of_nonneg_right (norm_add_le _ _) (nrm_nonneg_jl k z)).trans (by rw [add_mul]; exact add_le_add (h₁ z x) (h₂ z x))⟩⟩
      smul_mem' := fun c f hf => ⟨fun x => ⟨continuous_const.mul (hf.hol x).1,
                                            fun z v => hol1_const_mul c ((hf.hol x).2 z v)⟩,
        fun γ z x => by simp [hf.aut]; ring, fun z x h => by simp [hf.lev]; ring,
        let ⟨C, h⟩ := hf.bdd
        ⟨‖c‖ * C, fun z x => by rw [Pi.smul_apply, smul_eq_mul, norm_mul,
                                    mul_assoc]; exact mul_le_mul_of_nonneg_left (h z x) (norm_nonneg c)⟩⟩ }
  have hM : D.M k = S := Submodule.span_eq S
  exact fun f => by rw [hM]; rfl

theorem forms_stable_under_operators_proof_jl : FormsStableUnderOperators := by
  intro F I Gf _ _ _ D _ k
  refine ⟨isForm_sub D k, fun ι _ a ha f hf => ?_⟩
  rw [isForm_sub] at hf ⊢
  obtain ⟨C, hC⟩ := hf.bdd
  exact ⟨fun x => ⟨continuous_finsetSum _ fun i _ => (hf.hol (x * a i)).1,
      fun z v => hol1_finset_sum Finset.univ _ fun i _ => (hf.hol (x * a i)).2 z v⟩,
    fun γ z x => by change ∑ i, f (D.act γ z, D.j γ * x * a i) = D.J k γ z * ∑ i, f (z, x * a i)
                    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc,
                                                                                      hf.aut],
    fun z x h => ha (fun y => f (z, y)) (fun y h' => hf.lev z y h') x h,
    ⟨Fintype.card ι * C,
     fun z x => (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (nrm_nonneg_jl k z)).trans $ by
      rw [Finset.sum_mul]; exact (Finset.sum_le_sum fun i _ => hC z (x * a i)).trans (by simp)⟩⟩

-- === E3: Cusp region volume finite ===

theorem cusp_region_volume_finite_proof_jl : B1a → UpperHalfPlaneMeasureCoordinates → C2 → E0a → E0d → E3 := by
  intro hB1a _ _ hE0a _ F I Gf _ _ _ D hD b hb
  obtain ⟨hcnt, hsf, -, hPY, -⟩ := hE0a F I Gf D hD
  have : Countable (PG F) := hcnt; have : SigmaFinite (volume : Measure D.Xs) := hsf
  have : SigmaFinite (volume : Measure P) := hB1a.1; have : Countable D.Om := hD.cO
  obtain ⟨c₀, hc₀, hmink⟩ := hD.mink; obtain ⟨S, C, c, hc, hnorm⟩ := hD.normal c₀ hc₀
  let B1 : Set {z : ℂ // z.im ≠ 0} := {w | |w.1.re| ≤ C ∧ c ≤ |w.1.im|}
  have hB1m : MeasurableSet B1 :=
    (measurableSet_le (continuous_abs.comp (continuous_re.comp continuous_subtype_val)).measurable measurable_const).inter
      (measurableSet_le measurable_const (continuous_abs.comp (continuous_im.comp continuous_subtype_val)).measurable)
  have hB1fin : (volume : Measure P) B1 < ∞ := by
    have hK0 : 0 ≤ (1 + C ^ 2) * (1 + 1 / c ^ 2) := by positivity
    have hG : ∫⁻ t : ℂ, oR ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) < ∞ :=
      ((Complex.volume_preserving_equiv_real_prod.integrable_comp
        (integrable_inv_one_add_sq.mul_prod integrable_inv_one_add_sq).aestronglyMeasurable).2
        (integrable_inv_one_add_sq.mul_prod integrable_inv_one_add_sq)).lintegral_lt_top
    have hpt (t : ℂ) (h1 : |t.re| ≤ C) (h2 : c ≤ |t.im|) :
        1 / t.im ^ 2 ≤ (1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) := by
      have hc2 : 0 < c ^ 2 := by positivity
      have hb : c ^ 2 ≤ t.im ^ 2 := by nlinarith [sq_abs t.im,
                                                  mul_nonneg (sub_nonneg.2 h2) (add_nonneg (abs_nonneg t.im) hc.le)]
      have ha : t.re ^ 2 ≤ C ^ 2 := by nlinarith [sq_abs t.re,
                                                  mul_nonneg (sub_nonneg.2 h1) (by linarith [abs_nonneg t.re] : 0 ≤ C + |t.re|)]
      have e1 : 1 ≤ (1 + C ^ 2) * (1 + t.re ^ 2)⁻¹ := by rw [← div_eq_mul_inv,
                                                             le_div_iff₀ (by positivity)]; linarith
      have e2 : 1 / t.im ^ 2 ≤ (1 + 1 / c ^ 2) * (1 + t.im ^ 2)⁻¹ := by
        have : 1 ≤ t.im ^ 2 / c ^ 2 := (le_div_iff₀ hc2).2 (by linarith)
        rw [← div_eq_mul_inv, div_le_div_iff₀ (hc2.trans_le hb) (by positivity), add_mul, one_mul,
            one_div, inv_mul_eq_div]; linarith
      calc _ = 1 * (1 / t.im ^ 2) := (one_mul _).symm
        _ ≤ _ := mul_le_mul e1 e2 (by positivity) (by positivity)
        _ = _ := by ring
    change (Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume).withDensity (fun z => oR (1 / z.1.im ^ 2)) B1 < ∞
    rw [withDensity_apply _ hB1m]
    calc _ ≤ ∫⁻ z : {z : ℂ // z.im ≠ 0}, oR ((1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + z.1.re ^ 2)⁻¹ * (1 + z.1.im ^ 2)⁻¹))
              ∂(Measure.comap Subtype.val volume) :=
            (setLIntegral_mono' hB1m fun z hz => ENNReal.ofReal_le_ofReal (hpt z.1 hz.1 hz.2)).trans (setLIntegral_le_lintegral _ _)
      _ ≤ ∫⁻ t : ℂ, oR ((1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹)) :=
            (lint_comap isOpen_U_jl.measurableSet volume fun t : ℂ => oR ((1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹))).trans_le
              (setLIntegral_le_lintegral _ _)
      _ = oR ((1 + C ^ 2) * (1 + 1 / c ^ 2)) * ∫⁻ t : ℂ, oR ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) := by
            simp_rw [ENNReal.ofReal_mul hK0]; exact lintegral_const_mul _ (by fun_prop)
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG
  let T : Set D.Om := (fun x : Gf => ((x : Gf ⧸ D.H) : D.Om)) '' (S : Set Gf)
  let B1P : Set P := B1
  let U : Set D.Xs := Set.univ.pi fun _ : I => B1P
  have hS : MeasurableSet (T ×ˢ U) :=
      MeasurableSet.of_discrete.prod (MeasurableSet.univ_pi fun _ => hB1m)
  have hcover (y : D.Y) : ∃ g : PG F, g • y ∈ T ×ˢ U := by
    obtain ⟨s, hs0, hs⟩ := hmink y.2 (D.rep y.1); obtain ⟨γ, hγ⟩ := row_exists s hs0
    set y' : D.Y := (γ : PG F) • y
    have h1 : c₀ ≤ D.Ht ![0, 1] y'.2 (D.rep y'.1) := by
      change c₀ ≤ D.HtY ![0, 1] ((γ : PG F) • y); rw [htY_smul_jl D hD ![0, 1] e01_ne γ y,
                                                      hγ]; exact hs
    obtain ⟨bb, -, ⟨x', hx'S, h, hhH, hjx⟩, hSg⟩ := hnorm y'.2 (D.rep y'.1) h1
    refine ⟨(bb : PG F) * (γ : PG F), ?_, ?_⟩
    · rw [mul_smul]
      have hm := D.mk_smulO bb (D.rep y'.1); rw [rep_spec_jl] at hm
      exact ⟨x', hx'S, by change ((x' : Gf ⧸ D.H) : D.Om) = (bb : PG F) • y'.1; rw [hm, hjx]
                          exact (QuotientGroup.eq.2 (by simpa using inv_mem hhH)).symm⟩
    · rw [mul_smul]; change (bb : PG F) • y'.2 ∈ U; rw [D.mk_smulX]
      exact fun v _ => ⟨(hSg v).1, (hSg v).2.1⟩
  refine (orbit_cover D.μY hPY b hb _ hS hcover).trans_lt ?_
  rw [Dat.μY, Measure.prod_prod]
  refine ENNReal.mul_lt_top (Measure.count_apply_lt_top.2 (S.finite_toSet.image _)) ?_
  change (Measure.pi fun _ : I => (volume : Measure P)) (Set.univ.pi fun _ : I => B1P) < ∞
  rw [Measure.pi_pi]; exact ENNReal.prod_lt_top fun _ _ => hB1fin

-- === E4 & faceMap_zero_comp_eq_one: Kernel transform & inverse symmetry ===

def tm_jl {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)
    (k : I → ℕ) (ω : D.Om) (w : X I) (p : X I × Gf) (g : GL2 F) : ℂ :=
  D.ee ((D.rep ω)⁻¹ * (D.j g)⁻¹ * p.2) * (qq k p.1 (D.act g w) * D.J k g w)

section KernLemmas
variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

lemma tm_supp_jl (k : I → ℕ) (ω : D.Om) (w : X I) (γ : PG F) (z : X I) (x : Gf)
    (h : γ • ω ≠ ((x : Gf ⧸ D.H) : D.Om)) : tm_jl D k ω w (z, x) γ.out = 0 := by
  unfold tm_jl; rw [Dat.ee, dite_eq_right, zero_mul]
  intro hm; apply h; rw [smulO_out_jl]; exact QuotientGroup.eq.2 (by simpa [mul_assoc] using hm)

lemma tm_center_jl (k : I → ℕ) (hc : D.Compat k) (ω : D.Om) (w : X I) (p : X I × Gf) (g c : GL2 F)
    (hcc : c ∈ Subgroup.center (GL2 F)) : tm_jl D k ω w p (g * c) = tm_jl D k ω w p g := by
  unfold tm_jl; set h : D.H := ⟨D.j c, D.cenH c hcc⟩
  have hz := Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ (D.cenC c hcc)) (D.rep ω)⁻¹
  have e : (D.rep ω)⁻¹ * (D.j (g * c))⁻¹ * p.2 = ((h⁻¹ : D.H) : Gf) * ((D.rep ω)⁻¹ * (D.j g)⁻¹ * p.2) := by
    rw [map_mul, _root_.mul_inv_rev, ← mul_assoc, ← mul_assoc, hz]; simp [h, mul_assoc]
  rw [e, ee_mul_left_jl, J_mul_jl, act_center_jl D c hcc, act_mul_jl, act_center_jl D c hcc,
      J_center_jl D k hc c hcc, map_inv]
  have hu : (((D.χ h)⁻¹ : ℂˣ) : ℂ) * (D.χ h : ℂ) = 1 := by rw [← Units.val_mul, inv_mul_cancel,
                                                               Units.val_one]
  linear_combination (D.ee ((D.rep ω)⁻¹ * (D.j g)⁻¹ * p.2) * (qq k p.1 (D.act g w) * D.J k g w)) * hu

lemma norm_tm_le_jl (hD : D.Ax) (k : I → ℕ) (hk : ∀ v,
                                             1 ≤ k v) (y : D.Y) (γ : PG F) (z : X I) (x : Gf) :
    ‖tm_jl D k y.1 y.2 (z, x) γ.out‖ ≤
      {δ : PG F | δ • y.1 = ((x : Gf ⧸ D.H) : D.Om)}.indicator (fun δ => Kap k z (D.act δ.out y.2)) γ *
        (cst_jl k * nrm k y.2 / nrm k z) := by
  by_cases hγ : γ • y.1 = ((x : Gf ⧸ D.H) : D.Om)
  · rw [indicator_of_mem (show γ ∈ {δ : PG F | δ • y.1 = ((x : Gf ⧸ D.H) : D.Om)} from hγ)]
    unfold tm_jl; rw [norm_mul]
    calc _ ≤ 1 * ‖qq k z (D.act γ.out y.2) * D.J k γ.out y.2‖ :=
        mul_le_mul_of_nonneg_right (norm_ee_le_jl D hD _) (norm_nonneg _)
      _ = _ := by rw [one_mul,
                      eq_div_of_mul_eq (nrm_pos_jl k z).ne' (norm_qJ_jl D k hk γ.out z y.2)]; ring
  · rw [tm_supp_jl D k y.1 y.2 γ z x hγ]; simp [hγ]

lemma kap_sum_real (hD : D.Ax) (hS : KapSum) (k : I → ℕ) (hk : ∀ v, 4 ≤ k v) (y : D.Y) :
    ∃ C : ℝ, ∀ (ω' : D.Om) (z : X I),
      Summable ({δ : PG F | δ • y.1 = ω'}.indicator fun δ => Kap k z (D.act δ.out y.2)) ∧
      ∑' δ, {δ : PG F | δ • y.1 = ω'}.indicator (fun δ => Kap k z (D.act δ.out y.2)) δ ≤ C := by
  obtain ⟨c₀, hc₀, hm⟩ := hD.mink; obtain ⟨s, hs, hsy⟩ := hm y.2 (D.rep y.1)
  obtain ⟨C, hC'⟩ := hS F I Gf D hD k hk c₀ hc₀
  refine ⟨max (C * (1 + D.HtY s y)) 0, fun ω' z => ?_⟩
  have hb := hC' y s hs hsy ω' z; simp only [smulX_out_jl] at hb
  have hsum : Summable fun γ : {γ : PG F // γ • y.1 = ω'} => Kap k z (D.act γ.1.out y.2) := by
    simpa [ENNReal.toReal_ofReal (Kap_nonneg_jl k _ _)] using ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)
  refine ⟨(summable_subtype_iff_indicator (s := {δ : PG F | δ • y.1 = ω'})).1 hsum, ?_⟩
  rw [← _root_.tsum_subtype]
  exact (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 $
    (ENNReal.ofReal_tsum_of_nonneg (fun _ => Kap_nonneg_jl k _ _) hsum).trans_le
      (hb.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))

end KernLemmas

theorem kernel_level_transform_proof_jl : B1a → B1b → B1c → E0d → KapSum → KapInt → E4 := by
  intro _ _ _ _ hS hI F I Gf _ _ _ D hD k hk hc y
  have hk1 : ∀ v, 1 ≤ k v := fun v => le_trans (by norm_num) (hk v)
  obtain ⟨C, hC'⟩ := kap_sum_real D hD hS k hk y
  obtain ⟨C', A, hA⟩ := hI I k hk
  have hnrmc : Continuous (nrm k : X I → ℝ) := continuous_finsetProd _ fun v _ =>
    (continuous_abs.comp (continuous_im.comp (continuous_subtype_val.comp (continuous_apply v)))).rpow_const fun _ => Or.inr (by positivity)
  have hnear x (z₀ : X I) : ∃ U : Set (X I), IsOpen U ∧ z₀ ∈ U ∧ ∃ M : ℝ, ∀ z ∈ U, ∀ γ : PG F,
      ‖tm_jl D k y.1 y.2 (z,
                          x) γ.out‖ ≤ {δ : PG F | δ • y.1 = ((x : Gf ⧸ D.H) : D.Om)}.indicator (fun δ => Kap k z₀ (D.act δ.out y.2)) γ * M := by
    have hn0 := nrm_pos_jl k z₀
    refine ⟨(⋂ v, {z : X I | 1 / 2 < kap (z v) (z₀ v)}) ∩ {z | nrm k z₀ / 2 < nrm k z},
      (isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (cont_kap.comp ((continuous_apply v).prodMk continuous_const))).inter
        (isOpen_lt continuous_const hnrmc),
      ⟨mem_iInter.2 fun v => by show 1 / 2 < kap (z₀ v) (z₀ v); rw [kap_self]; norm_num,
       by show nrm k z₀ / 2 < nrm k z₀; linarith⟩,
      A * (cst_jl k * nrm k y.2 / (nrm k z₀ / 2)), fun z ⟨hz1,
                                                          hz2⟩ γ => (norm_tm_le_jl D hD k hk1 y γ z x).trans ?_⟩
    by_cases hγ : γ • y.1 = ((x : Gf ⧸ D.H) : D.Om)
    · rw [indicator_of_mem (show γ ∈ {δ : PG F | δ • y.1 = ((x : Gf ⧸ D.H) : D.Om)} from hγ),
          indicator_of_mem (show γ ∈ {δ : PG F | δ • y.1 = ((x : Gf ⧸ D.H) : D.Om)} from hγ)]
      have hK : Kap k z (D.act γ.out y.2) ≤ A * Kap k z₀ (D.act γ.out y.2) := by
        rw [Kap_symm_jl k z,
            Kap_symm_jl k z₀]; exact ((hA (D.act γ.out y.2)).2.2.2 z z₀ fun v => (mem_iInter.1 hz1 v).le).1
      have hc0 : 0 ≤ cst_jl k * nrm k y.2 := mul_nonneg (cst_nonneg_jl k hk1) (nrm_nonneg_jl k _)
      calc _ ≤ (A * Kap k z₀ (D.act γ.out y.2)) * (cst_jl k * nrm k y.2 / (nrm k z₀ / 2)) :=
            mul_le_mul hK (div_le_div_of_nonneg_left hc0 (by linarith) hz2.le) (div_nonneg hc0 (nrm_pos_jl k z).le) (mul_nonneg A.2 (Kap_nonneg_jl k _ _))
        _ = _ := by ring
    · simp [hγ]
  have htm_cont x (g : GL2 F) : Continuous fun z : X I => tm_jl D k y.1 y.2 (z, x) g := by
    have h1 v : Continuous fun z : I → P => (z v,
                                             D.act g y.2 v) := (continuous_apply v).prodMk continuous_const
    unfold tm_jl qq; dsimp only
    exact continuous_const.mul ((continuous_finsetProd _ fun v _ => (cont_q1 (k v)).comp (h1 v)).mul continuous_const)
  refine ⟨fun x => ⟨continuous_iff_continuousAt.2 fun z₀ => by
        obtain ⟨U, hU, hz₀, M, hM⟩ := hnear x z₀
        exact (continuousOn_tsum (fun γ : PG F => (htm_cont x γ.out).continuousOn) ((hC' ((x : Gf ⧸ D.H) : D.Om) z₀).1.mul_right M)
          fun γ z hz => hM z hz γ).continuousAt (hU.mem_nhds hz₀),
      fun z v t₀ ht₀ => by
        obtain ⟨U, hU, hmem, M, hM⟩ := hnear x (update z v ⟨t₀, ht₀⟩)
        let U' : Set P := (update z v) ⁻¹' U
        have hU' : IsOpen U' := hU.preimage (continuous_const.update v continuous_id)
        let V : Set ℂ := Subtype.val '' U'
        have hV : IsOpen V := isOpen_U_jl.isOpenMap_subtype_val U' hU'
        have htm_hol (γ : PG F) : Hol1 fun t => tm_jl D k y.1 y.2 (update z v t, x) γ.out := by
          have e1 (s : P) : tm_jl D k y.1 y.2 (update z v s, x) γ.out =
              (D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x) * (∏ u ∈ Finset.univ.erase v,
                                                           q1 (k u) (z u) (D.act γ.out y.2 u)) * D.J k γ.out y.2) *
                q1 (k v) s (D.act γ.out y.2 v) := by
            unfold tm_jl qq; dsimp only; rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ v),
                                             update_self]
            rw [Finset.prod_congr rfl fun u hu => by rw [update_of_ne (ne_of_mem_erase hu)]]; ring
          have e : ext1 (fun t => tm_jl D k y.1 y.2 (update z v t,
                                                     x) γ.out) = fun t => _ * ext1 (fun s => q1 (k v) s (D.act γ.out y.2 v)) t :=
            funext fun t => by unfold ext1; split_ifs with ht; exact e1 _; exact (mul_zero _).symm
          unfold Hol1; rw [e]; exact (hol_q1 (k v) _).const_mul _
        have hd : DifferentiableOn ℂ (fun t => ∑' γ : PG F,
                                      ext1 (fun s => tm_jl D k y.1 y.2 (update z v s,
                                                                        x) γ.out) t) V :=
          Complex.differentiableOn_tsum_of_summable_norm ((hC' ((x : Gf ⧸ D.H) : D.Om) (update z v ⟨t₀, ht₀⟩)).1.mul_right M)
            (fun γ => (htm_hol γ).mono (by rintro _ ⟨s, _, rfl⟩; exact s.2)) hV
            (by rintro γ _ ⟨s, hs,
                            rfl⟩; exact (congrArg norm (ext1_of_im _ s.2)).trans_le (hM _ hs γ))
        have hin : t₀ ∈ V := ⟨⟨t₀, ht₀⟩, hmem, rfl⟩
        exact ((hd.differentiableAt (hV.mem_nhds hin)).congr_of_eventuallyEq $ by
          filter_upwards [hV.mem_nhds hin] with t ht; obtain ⟨s, _, rfl⟩ := ht
          exact (ext1_of_im _ s.2).trans (tsum_congr fun γ => (ext1_of_im (fun s => tm_jl D k y.1 y.2 (update z v s, x) γ.out) s.2).symm)).differentiableWithinAt⟩,
    fun γ z x => ?_, fun z x h => ?_, ?_⟩
  · change ∑' δ : PG F, tm_jl D k y.1 y.2 (D.act γ z,
                                           D.j γ * x) δ.out = D.J k γ z * ∑' δ : PG F, tm_jl D k y.1 y.2 (z, x) δ.out
    rw [← Equiv.tsum_eq (Equiv.mulLeft (γ : PG F)), ← tsum_mul_left]
    refine tsum_congr fun δ => ?_
    have hmk : ((γ * δ.out : GL2 F) : PG F) = (γ : PG F) * δ := by rw [QuotientGroup.mk_mul,
                                                                       QuotientGroup.out_eq']
    have h2 := QuotientGroup.eq.1 (by rw [hmk,
                                          QuotientGroup.out_eq'] : (((γ * δ.out : GL2 F) : PG F) = (((γ : PG F) * δ).out : PG F)))
    have heq : tm_jl D k y.1 y.2 (D.act γ z,
                                  D.j γ * x) ((γ : PG F) * δ).out = tm_jl D k y.1 y.2 (D.act γ z,
                                                                                       D.j γ * x) (γ * δ.out) :=
      (congrArg (tm_jl D k y.1 y.2 _) (show ((γ : PG F) * δ).out = (γ * δ.out) * ((γ * δ.out)⁻¹ * ((γ : PG F) * δ).out) by group)).trans
        (tm_center_jl D k hc _ _ _ _ _ h2)
    refine heq.trans ?_; unfold tm_jl
    rw [show (D.rep y.1)⁻¹ * (D.j (γ * δ.out))⁻¹ * (D.j γ * x) = (D.rep y.1)⁻¹ * (D.j δ.out)⁻¹ * x by rw [map_mul]; group]
    have hqJ : qq k (D.act γ z) (D.act (γ * δ.out) y.2) * D.J k (γ * δ.out) y.2 = D.J k γ z * (qq k z (D.act δ.out y.2) * D.J k δ.out y.2) := by
      simp only [qq, Dat.J, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v _ => by
        change q1 (k v) (D.r v γ • z v) (D.r v (γ * δ.out) • y.2 v) * j1 (k v) (D.r v (γ * δ.out)) (y.2 v) = _
        rw [map_mul, mul_smul, j1_mul, ← mul_assoc, q1_smul, mul_assoc]; rfl
    rw [hqJ]; ring
  · change ∑' δ : PG F, tm_jl D k y.1 y.2 (z,
                                           x * h) δ.out = D.χ h * ∑' δ : PG F, tm_jl D k y.1 y.2 (z,
                                                                                                  x) δ.out
    rw [← tsum_mul_left]; refine tsum_congr fun δ => by
      unfold tm_jl; rw [show (D.rep y.1)⁻¹ * (D.j δ.out)⁻¹ * (x * h) = (D.rep y.1)⁻¹ * (D.j δ.out)⁻¹ * x * h by group, ee_mul_right_jl]; ring
  · refine ⟨C * (cst_jl k * nrm k y.2), fun z x => ?_⟩
    obtain ⟨hs, hle⟩ := hC' ((x : Gf ⧸ D.H) : D.Om) z
    have h1 :=
        tsum_of_norm_bounded (hs.hasSum.mul_right _) fun γ => norm_tm_le_jl D hD k hk1 y γ z x
    have hn := nrm_pos_jl k z
    calc _ ≤ _ * nrm k z := mul_le_mul_of_nonneg_right h1 hn.le
      _ = _ * (cst_jl k * nrm k y.2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hle (mul_nonneg (cst_nonneg_jl k hk1) (nrm_nonneg_jl k _))

theorem kernel_inverse_symmetry_jl : B1a → B1b → B1c → E0a → E0d → KapSum → faceMap_zero_comp_eq_one := by
  intro _ _ _ hE0a _ hKS F I Gf _ _ _ D hAx k hk _ p
  obtain ⟨hcount, -, -, -, -, -, hborel, -⟩ := hE0a F I Gf D hAx
  obtain ⟨c₀, hc₀, hmink⟩ := hAx.mink; obtain ⟨C, hCb⟩ := hKS F I Gf D hAx k hk c₀ hc₀
  let xH : D.Om := (p.2 : Gf ⧸ D.H); let zX : D.Xs := p.1
  obtain ⟨s, hs, hsle⟩ := hmink p.1 (D.rep xH)
  set Bnd := max (C * (1 + D.HtY s (xH, p.1))) 0
  have hT (y : D.Y) : ∑' γ : PG F, ‖tm_jl D k y.1 y.2 p γ.out‖ₑ ≤ oR (cst_jl k / nrm k p.1 * nrm k y.2) * oR Bnd := by
    have hk1 : ∀ v, 1 ≤ k v := fun v => le_trans (by norm_num) (hk v)
    have hle γ : ‖tm_jl D k y.1 y.2 p γ.out‖ₑ ≤ {γ : PG F | γ • y.1 = xH}.indicator
        (fun γ => oR (cst_jl k / nrm k p.1 * nrm k y.2) * oR (Kap k y.2 (γ⁻¹ • zX : D.Xs))) γ := by
      by_cases hγ : γ • y.1 = xH
      · rw [indicator_of_mem (show γ ∈ {γ : PG F | γ • y.1 = xH} from hγ)]
        have h1' : ‖tm_jl D k y.1 y.2 p γ.out‖ ≤ cst_jl k / nrm k p.1 * nrm k y.2 * Kap k y.2 (γ⁻¹ • zX : D.Xs) :=
          (norm_tm_le_jl D hAx k hk1 y γ p.1 p.2).trans_eq $ by
            rw [indicator_of_mem (show γ ∈ {δ : PG F | δ • y.1 = xH} from hγ), ← smulX_out_jl,
                Kap_swap_jl D k γ p.1 y.2]; ring
        exact (ofReal_norm _).symm.trans_le $ (ENNReal.ofReal_le_ofReal h1').trans_eq
          (ENNReal.ofReal_mul (mul_nonneg (div_nonneg (cst_nonneg_jl k hk1) (nrm_nonneg_jl k _)) (nrm_nonneg_jl k _)))
      · rw [indicator_of_notMem (show γ ∉ {γ : PG F | γ • y.1 = xH} from hγ),
            tm_supp_jl D k y.1 y.2 γ p.1 p.2 hγ]; simp
    have h1 := ENNReal.tsum_le_tsum hle; rw [← _root_.tsum_subtype, ENNReal.tsum_mul_left] at h1
    let invE : {γ : PG F // γ • y.1 = xH} ≃ {δ : PG F // δ • xH = y.1} :=
      ⟨fun γ => ⟨γ.1⁻¹, by rw [inv_smul_eq_iff, γ.2]⟩, fun δ => ⟨δ.1⁻¹, by rw [inv_smul_eq_iff,
                                                                               δ.2]⟩,
       fun _ => Subtype.ext (inv_inv _), fun _ => Subtype.ext (inv_inv _)⟩
    refine h1.trans $ by
      gcongr
      exact (invE.tsum_eq (fun δ => oR (Kap k y.2 (δ.1 • zX : D.Xs)))).trans_le
        ((hCb (xH, p.1) s hs hsle y.1 y.2).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hsumm (y : D.Y) : Summable fun γ : PG F => ‖tm_jl D k y.1 y.2 p γ.out‖ := by
    simpa only [toReal_enorm] using ENNReal.summable_toReal (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hT y))
  have hc0 : 0 ≤ cst_jl k / nrm k p.1 :=
      div_nonneg (cst_nonneg_jl k fun v => le_trans (by norm_num) (hk v)) (nrm_nonneg_jl k _)
  refine ⟨hsumm, ?_, ⟨cst_jl k / nrm k p.1 * Bnd,
                      fun y => (norm_tsum_le_tsum_norm (hsumm y)).trans ?_⟩⟩
  · have := hcount; have := hborel
    have hTm (γ : PG F) : Measurable (fun y : D.Y => tm_jl D k y.1 y.2 p γ.out) :=
      ((Measurable.of_discrete (f := fun ω : D.Om => D.ee ((D.rep ω)⁻¹ * (D.j γ.out)⁻¹ * p.2))).comp measurable_fst).mul
        (((continuous_finsetProd _ fun v _ => (cont_q1 (k v)).comp (continuous_const.prodMk ((cont_smul_P (D.r v γ.out)).comp (continuous_apply v)))).mul
          (continuous_finsetProd _ fun v _ => (cont_j1 (k v) (D.r v γ.out)).comp (continuous_apply v))).measurable.comp measurable_snd)
    exact measurable_of_tendsto_metrizable' atTop (fun s => Finset.measurable_sum s fun γ _ => hTm γ)
      (tendsto_pi_nhds.2 fun y => (hsumm y).of_norm.hasSum)
  · refine ((tsum_congr fun γ : PG F => (toReal_enorm _).symm).trans (ENNReal.tsum_toReal_eq fun _ => enorm_ne_top).symm).trans_le ?_
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg hc0 (le_max_right _ _)) (nrm_nonneg_jl k _)) $
      (hT y).trans_eq ((ENNReal.ofReal_mul (mul_nonneg hc0 (nrm_nonneg_jl k _))).symm.trans (congrArg oR (by ring)))

-- === C3: Inverse series summable ===

theorem inverse_series_summable_jl : C3 := by
  intro G Y _ _ _ _ μ hμ b hb f hf hfi
  let Φ (g : G) (y : Y) := b y • f (g • y)
  let Ψ (g : G) (y : Y) := b (g⁻¹ • y) • f y
  have hΦm g : Measurable (Φ g) := hb.meas.smul (hf.comp (hμ g).measurable)
  have hΨm g : Measurable (Ψ g) := (hb.meas.comp (hμ g⁻¹).measurable).smul hf
  have hhs y : HasSum (fun g : G => b (g⁻¹ • y)) 1 := (Equiv.inv G).hasSum_iff.2 (hb.sum y)
  have hΦl g : ∫⁻ y, ‖Φ g y‖ₑ ∂μ = ∫⁻ z, ‖Ψ g z‖ₑ ∂μ := by
    rw [← (hμ g).lintegral_comp (hΨm g).enorm]; exact lintegral_congr fun y => by simp [Φ, Ψ]
  have hsumΨ : ∑' g, ∫⁻ z, ‖Ψ g z‖ₑ ∂μ = ∫⁻ z, ‖f z‖ₑ ∂μ := by
    calc _ = ∑' g, ∫⁻ z, oR (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ :=
        tsum_congr fun g => lintegral_congr fun z => by
              dsimp only [Ψ]; rw [enorm_smul, Real.enorm_eq_ofReal (hb.nonneg _)]
      _ = ∫⁻ z, ∑' g, oR (b (g⁻¹ • z)) * ‖f z‖ₑ ∂μ :=
            (lintegral_tsum fun g => ((hb.meas.comp (hμ g⁻¹).measurable).ennreal_ofReal.mul hf.enorm).aemeasurable).symm
      _ = _ := lintegral_congr fun z => by
            rw [ENNReal.tsum_mul_right,
                ← ENNReal.ofReal_tsum_of_nonneg (fun _ => hb.nonneg _) (hhs z).summable,
              (hhs z).tsum_eq, ENNReal.ofReal_one, one_mul]
  have hsumΦ : ∑' g, ∫⁻ y, ‖Φ g y‖ₑ ∂μ ≠ ∞ := by rw [tsum_congr hΦl, hsumΨ]; exact hfi.2.ne
  have hfun : (fun y => b y • ∑' g : G,
               f (g • y)) = fun y => ∑' g, Φ g y := funext fun y => (tsum_const_smul'' (b y)).symm
  refine ⟨by rw [hfun]; refine ⟨AEStronglyMeasurable.tsum fun g => (hΦm g).aestronglyMeasurable, ?_⟩
             exact ((lintegral_mono fun _ => enorm_tsum_le_tsum_enorm).trans_eq (lintegral_tsum fun g => (hΦm g).enorm.aemeasurable)).trans_lt hsumΦ.lt_top,
    ?_⟩
  rw [hfun, integral_tsum (fun g => (hΦm g).aestronglyMeasurable) hsumΦ,
    tsum_congr fun g => (integral_congr_ae (ae_of_all _ fun y => by simp [Φ,
                                                                          Ψ])).trans ((hμ g).integral_comp (actEquiv_jl hμ g).measurableEmbedding (Ψ g)),
    ← integral_tsum (fun g => (hΨm g).aestronglyMeasurable) (hsumΨ.symm ▸ hfi.2.ne)]
  exact integral_congr_ae (ae_of_all _ fun z => by dsimp only [Ψ]; rw [((hhs z).smul_const (f z)).tsum_eq, one_smul])

-- === B2: Cayley transform ===

def cay_jl (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

lemma im_cay_jl (w : ℂ) : (cay_jl w).im = (1 - normSq w) / normSq (1 - w) := by
  rw [cay_jl, Complex.div_im, normSq_apply w]
  simp only [mul_im, mul_re, I_re, I_im, add_re, add_im, one_re, one_im, sub_re, sub_im]; ring

theorem cayley_transform_proof_jl : B2 := by
  intro h h0 hi
  have hS := isOpen_U_jl.measurableSet
  -- Step 1: P -> {t : ℂ | 0 < t.im}
  let U0 : Set ℂ := {t : ℂ | t.im ≠ 0}
  let h' : U0 → ℂ := h
  let g (t : ℂ) : ℂ := ((1 / t.im ^ 2 : ℝ) : ℂ) * ext1 h t
  have h1 : IntegrableOn g {t : ℂ | 0 < t.im} ∧ ∫ z, h z = ∫ t in {t : ℂ | 0 < t.im}, g t := by
    have hρ : Measurable fun z : U0 => oR (1 / z.1.im ^ 2) := by fun_prop
    have hfin : ∀ᵐ z ∂(Measure.comap (Subtype.val : U0 → ℂ) volume), oR (1 / z.1.im ^ 2) < ∞ :=
      ae_of_all _ fun _ => ENNReal.ofReal_lt_top
    have key : (fun z : U0 => (oR (1 / z.1.im ^ 2)).toReal • h' z) = g ∘ Subtype.val :=
        funext fun z => by
      rw [ENNReal.toReal_ofReal (by positivity)]; simp only [g, h', Function.comp_apply, real_smul,
                                                             ext1_of_im h z.2]; rfl
    have iS : IntegrableOn g U0 := by
      rw [integrableOn_iff_comap_subtypeVal hS,
          ← key]; exact (integrable_withDensity_iff_integrable_smul' hρ hfin).1 hi
    refine ⟨iS.mono_set fun _ ht => ne_of_gt ht, ?_⟩
    change ∫ z : U0, h' z ∂((Measure.comap Subtype.val volume).withDensity fun z => oR (1 / z.1.im ^ 2)) = _
    rw [integral_withDensity_eq_integral_toReal_smul hρ hfin, key]
    change ∫ z : U0, g z.1 ∂Measure.comap Subtype.val volume = _
    rw [integral_subtype_comap hS g]
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS (fun _ ht => ne_of_gt ht) fun t ⟨ht1,
                                                                                               ht2⟩ => by
      simp [g, ext1, h0 ⟨t, ht1⟩ (lt_of_le_of_ne (not_lt.1 ht2) ht1)]
  -- Step 2: {0 < t.im} -> ball 0 1 via cay_jl
  have hne1 {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : w ≠ 1 := by rintro rfl; simp at hw
  have himg : cay_jl '' ball (0 : ℂ) 1 = {t : ℂ | 0 < t.im} := Set.ext fun t =>
    ⟨by rintro ⟨w, hw, rfl⟩
        have hn : normSq w < 1 :=
            by rw [mem_ball_zero_iff] at hw; rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
        show 0 < (cay_jl w).im; rw [im_cay_jl]; exact div_pos (by linarith) (normSq_pos.2 (sub_ne_zero.2 (hne1 hw).symm)),
     fun (ht : 0 < t.im) => by
      have hd : t + I ≠ 0 := fun h => by have := congrArg im h; simp at this; linarith
      refine ⟨(t - I) / (t + I), ?_, ?_⟩
      · rw [mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.2 hd),
            ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
          ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]; simp [normSq_apply]; nlinarith
      · have h3 : 1 - (t - I) / (t + I) ≠ 0 := by rw [one_sub_div hd]; simp [hd]
        rw [cay_jl, div_eq_iff h3]; field_simp; ring⟩
  have hinj : InjOn cay_jl (ball (0 : ℂ) 1) := fun a ha b hb hab => by
    have h1 := sub_ne_zero.2 (hne1 ha).symm; have h2 := sub_ne_zero.2 (hne1 hb).symm
    rw [cay_jl, cay_jl, div_eq_div_iff h1 h2] at hab
    simpa [sub_eq_zero] using (show I * (2 * (a - b)) = 0 by linear_combination hab)
  let D w := (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * I / (1 - w) ^ 2)).restrictScalars ℝ
  have hf' w (hw : w ∈ ball (0 : ℂ) 1) : HasFDerivWithinAt cay_jl (D w) (ball 0 1) w := by
    have hd : HasDerivAt cay_jl (2 * I / (1 - w) ^ 2) w :=
      ((((hasDerivAt_id w).const_add 1).const_mul I).div ((hasDerivAt_id w).const_sub 1) (sub_ne_zero.2 (hne1 hw).symm)).congr_deriv (by simp; ring)
    exact (hd.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  let F (w : ℂ) : ℂ := ((4 / (1 - normSq w) ^ 2 : ℝ) : ℂ) * ext1 h (cay_jl w)
  have hpt2 : EqOn (fun w => |(D w).det| • g (cay_jl w)) F (ball 0 1) := fun w hw => by
    have hn : normSq w < 1 :=
        by rw [mem_ball_zero_iff] at hw; rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
    have h1w : 0 < normSq (1 - w) := normSq_pos.2 (sub_ne_zero.2 (hne1 hw).symm)
    have hdet : |(D w).det| = 4 / normSq (1 - w) ^ 2 := by
      rw [show (D w).det = normSq (2 * I / (1 - w) ^ 2) by simp [D, ContinuousLinearMap.det,
                                                                 LinearMap.det_restrictScalars, Algebra.norm_complex_eq],
        abs_of_nonneg (normSq_nonneg _), map_div₀, map_pow, map_mul]; simp [normSq_apply]; norm_num
    simp only [hdet, g, F, real_smul, im_cay_jl, ← mul_assoc, ← ofReal_mul]; congr 2; field_simp
  have h2 : IntegrableOn F (ball 0 1) ∧ ∫ t in {t : ℂ | 0 < t.im}, g t = ∫ w in ball (0 : ℂ) 1, F w := by
    rw [← himg] at h1 ⊢
    exact ⟨((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume measurableSet_ball hf' hinj g).1 h1.1).congr_fun hpt2 measurableSet_ball,
      by rw [integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_ball hf' hinj]; exact setIntegral_congr_fun measurableSet_ball hpt2⟩
  -- Step 3: ball 0 1 -> Ioo 0 1 ×ˢ Ioo (-π) π via polarCoord
  let S := Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π
  have hSm : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hp := Complex.volume_preserving_equiv_real_prod.symm
  have hsub : polarCoord.symm '' S ⊆ measurableEquivRealProd.symm ⁻¹' ball 0 1 := by
    rintro _ ⟨p, hp', rfl⟩
    simp only [Set.mem_preimage, mem_ball_zero_iff,
               measurableEquivRealProd_symm_polarCoord_symm_apply, norm_polarCoord_symm, abs_of_pos hp'.1.1]; exact hp'.1.2
  have hae : polarCoord.symm '' S =ᵐ[volume] measurableEquivRealProd.symm ⁻¹' ball 0 1 := by
    filter_upwards [polarCoord_source_ae_eq_univ] with q hq
    have hq' : q ∈ polarCoord.source := by rw [hq]; trivial
    try rw [eq_iff_iff]
    refine ⟨fun h => hsub h, fun hqT => ⟨polarCoord q, ⟨⟨(polarCoord.map_source hq').1, ?_⟩,
                                                                (polarCoord.map_source hq').2⟩, polarCoord.left_inv hq'⟩⟩
    change measurableEquivRealProd.symm q ∈ ball (0 : ℂ) 1 at hqT
    rw [mem_ball_zero_iff, show ‖measurableEquivRealProd.symm q‖ = √(q.1 ^ 2 + q.2 ^ 2) by
      change ‖equivRealProd.symm q‖ = _; rw [equivRealProd_symm_apply, Complex.norm_def,
                                             normSq_add_mul_I]] at hqT
    simpa using hqT
  have hG' :=
      ((hp.integrableOn_comp_preimage measurableEquivRealProd.symm.measurableEmbedding).2 h2.1).mono_set hsub
  have hder : ∀ p ∈ S, HasFDerivWithinAt polarCoord.symm (fderivPolarCoordSymm p) S p :=
      fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt
  have hinj3 : InjOn polarCoord.symm S :=
      polarCoord.symm.injOn.mono fun p hp => show p.1 ∈ Ioi (0 : ℝ) ∧ p.2 ∈ Ioo (-π) π from ⟨hp.1.1,
                                                                                             hp.2⟩
  have hpt3 : EqOn (fun p : ℝ × ℝ => |(fderivPolarCoordSymm p).det| • (F ∘ measurableEquivRealProd.symm) (polarCoord.symm p))
      (fun p : ℝ × ℝ => ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) * ext1 h (cay_jl (circleMap 0 p.1 p.2))) S := by
    rintro ⟨r, θ⟩ ⟨hr, _⟩
    simp only [det_fderivPolarCoordSymm, abs_of_pos hr.1, Function.comp_apply,
               measurableEquivRealProd_symm_polarCoord_symm_apply,
      Complex.polarCoord_symm_apply, real_smul, F, show (r : ℂ) * (Real.cos θ + Real.sin θ * I) = circleMap 0 r θ by
        rw [circleMap, zero_add, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin],
      show normSq (circleMap 0 r θ) = r ^ 2 by rw [normSq_eq_norm_sq, norm_circleMap_zero,
                                                   abs_of_pos hr.1]]
    push_cast; ring
  refine ⟨((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hSm hder hinj3 _).1 hG').congr_fun hpt3 hSm, ?_⟩
  rw [h1.2, h2.2,
      ← hp.setIntegral_preimage_emb measurableEquivRealProd.symm.measurableEmbedding F (ball 0 1),
    ← setIntegral_congr_set hae, integral_image_eq_integral_abs_det_fderiv_smul volume hSm hder hinj3]
  exact setIntegral_congr_fun hSm hpt3

end UpperTheory.Esk

-- ==== B3

noncomputable section

open MeasureTheory Matrix Finset Filter Function Subgroup MulAction QuotientGroup Topology Metric
open Set hiding center
open Real hiding dist_eq
open _root_.Complex hiding log exp exp_add exp_neg exp_log exp_nat_mul log_mul log_exp exp_sub
open scoped ENNReal NNReal ComplexConjugate Classical Real

namespace UpperTheory.Esk

-- === B3: 1D Reproducing formula ===

theorem reproducing_formula_proof_jl : B1a → B1b → B1c → B2 → B6 → B3 := by
  intro _ _ _ hB2 hB6 k hk f hf ⟨C, hC⟩ z
  have cont_of_hol {g : P → ℂ} (hg : Hol1 g) : Continuous g := by
    have h1 : Continuous fun w : P => ext1 g w.1 :=
        hg.continuousOn.comp_continuous continuous_subtype_val fun w => w.2
    exact h1.congr fun w => ext1_coe g w
  have hint {g : P → ℂ} (hc : Continuous g) {C' : ℝ} (hC' : ∀ w : P,
                                                      ‖g w‖ * |w.1.im| ^ ((k : ℝ) / 2) ≤ C') (w0 : P) :
      Integrable fun w => q1 k w0 w * g w := by
    obtain ⟨C6, hC6⟩ := hB6 k hk
    have hki : Integrable fun w => kap w0 w ^ ((k : ℝ) / 2) :=
      ⟨((cont_kap.comp (continuous_const.prodMk continuous_id)).rpow_const fun _ => Or.inr (by positivity)).aestronglyMeasurable,
        by rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun w => rpow_nonneg (kap_nonneg_jl _ _) _)]; exact (hC6 w0).1.trans_lt ENNReal.coe_lt_top⟩
    have hA : 0 ≤ ((k : ℝ) - 1) / (4 * π) :=
        div_nonneg (by have : (4 : ℝ) ≤ k := (by exact_mod_cast hk); linarith) (by positivity)
    have hze : 0 < |w0.1.im| ^ ((k : ℝ) / 2) := rpow_pos_of_pos (abs_pos.2 w0.2) _
    refine (hki.const_mul (((k : ℝ) - 1) / (4 * π) * C' / |w0.1.im| ^ ((k : ℝ) / 2))).mono'
      (((cont_q1 k).comp (continuous_const.prodMk continuous_id)).mul hc).aestronglyMeasurable (ae_of_all _ fun w => ?_)
    have hq : ‖q1 k w0 w‖ = ((k : ℝ) - 1) / (4 * π) * kap w0 w ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2) / |w0.1.im| ^ ((k : ℝ) / 2) :=
      (eq_div_iff hze.ne').2 (norm_q1 k w0 w (by omega))
    rw [norm_mul, hq]
    calc _ = (((k : ℝ) - 1) / (4 * π) * kap w0 w ^ ((k : ℝ) / 2) / |w0.1.im| ^ ((k : ℝ) / 2)) * (‖g w‖ * |w.1.im| ^ ((k : ℝ) / 2)) :=
        by ring
      _ ≤ _ * C' :=
          mul_le_mul_of_nonneg_left (hC' w) (div_nonneg (mul_nonneg hA (rpow_nonneg (kap_nonneg_jl _ _) _)) hze.le)
      _ = _ := by ring
  refine ⟨hint (cont_of_hol hf) hC z, ?_⟩
  obtain ⟨g, -, -, rfl⟩ := trans_iP z
  let f' (w : P) := f (g • w) / j1 k g w
  have hf' : Hol1 f' := by
    have hc0 : ((|g.val.det| ^ (-(k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 :=
        by exact_mod_cast (rpow_pos_of_pos (abs_pos.2 g.det_ne_zero) _).ne'
    have hmob : DifferentiableOn ℂ (fun t => num g t / den g t) {t : ℂ | t.im ≠ 0} := fun t ht =>
      ((by unfold num; fun_prop : Differentiable ℂ (num g)) t |>.div ((by unfold den; fun_prop : Differentiable ℂ (den g)) t) (den_ne g ht)).differentiableWithinAt
    have h1 : DifferentiableOn ℂ (fun t => ext1 f (num g t / den g t) / (den g t ^ k * ((|g.val.det| ^ (-(k : ℝ) / 2) : ℝ) : ℂ))) {t | t.im ≠ 0} :=
      (hf.comp hmob fun t ht => let w : P := ⟨t, ht⟩; (g • w).2).div
        (fun t _ => ((((by unfold den; fun_prop : Differentiable ℂ (den g)) t).pow k).mul_const _).differentiableWithinAt)
        fun t ht => mul_ne_zero (pow_ne_zero _ (den_ne g ht)) hc0
    exact h1.congr fun t ht => by
      let w : P := ⟨t, ht⟩
      rw [ext1_of_im _ ht]; show f (g • w) / j1 k g w = _; rw [← ext1_coe f (g • w), coe_smul]; rfl
  have hC' (w : P) : ‖f' w‖ * |w.1.im| ^ ((k : ℝ) / 2) ≤ C := by
    have hj : ‖j1 k g w‖ ≠ 0 := norm_ne_zero_iff.2 (j1_ne k g w)
    calc ‖f (g • w) / j1 k g w‖ * |w.1.im| ^ ((k : ℝ) / 2) = ‖f (g • w)‖ * |(g • w).1.im| ^ ((k : ℝ) / 2) := by
          rw [← norm_j1 k g w, norm_div]; field_simp
      _ ≤ C := hC _
  have hat_i : ∫ w, q1 k iP w * f' w = f' iP := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have hvan (w : P) (hw : w.1.im < 0) : q1 (m + 2) iP w * f' w = 0 := by
      unfold q1; rw [ite_eq_right (by show ¬(0 < I.im * w.1.im); simp; linarith), zero_mul]
    obtain ⟨hIO, heq⟩ := hB2 (fun w => q1 (m + 2) iP w * f' w) hvan (hint (cont_of_hol hf') hC' iP)
    rw [heq]
    have hdisc {s : ℂ} (hs : ‖s‖ < 1) : 1 - s ≠ 0 ∧ 0 < (cay_jl s).im := by
      have h1 : 1 - s ≠ 0 := fun h => by have : s = 1 := (by linear_combination -h); rw [this,
                                                                                         norm_one] at hs; exact lt_irrefl _ hs
      exact ⟨h1,
             by rw [im_cay_jl]; exact div_pos (by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg s]) (normSq_pos.2 h1)⟩
    have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) :=
        measurableSet_Ioo.prod measurableSet_Ioo
    have hpt : EqOn (fun p : ℝ × ℝ => ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) * ext1 (fun w => q1 (m + 2) iP w * f' w) (cay_jl (circleMap 0 p.1 p.2)))
        (fun p : ℝ × ℝ => ((((m : ℝ) + 1) / π * p.1 * (1 - p.1 ^ 2) ^ m : ℝ) : ℂ) * (ext1 f' (cay_jl (circleMap 0 p.1 p.2)) / (1 - circleMap 0 p.1 p.2) ^ (m + 2)))
        (Set.Ioo 0 1 ×ˢ Set.Ioo (-π) π) := by
      rintro ⟨r, θ⟩ ⟨⟨hr0, hr1⟩, _⟩; dsimp only
      set s := circleMap 0 r θ; set w := cay_jl s
      have hns : ‖s‖ = r := by rw [norm_circleMap_zero, abs_of_pos hr0]
      obtain ⟨h1s, hwim⟩ := hdisc (hns.symm ▸ hr1)
      have hcs : s * conj s = (r : ℂ) ^ 2 := by rw [Complex.mul_conj, normSq_eq_norm_sq,
                                                    hns]; push_cast; ring
      have h1c : 1 - conj s ≠ 0 := fun h => h1s (by simpa using congrArg conj h)
      have hcw : conj w = -I * (1 + conj s) / (1 - conj s) := by simp [w, cay_jl]
      have hratio : (w - conj w) / (I - conj w) = (1 - (r : ℂ) ^ 2) / (1 - s) := by
        have hI := I_ne_zero
        rw [show w - conj w = 2 * I * (1 - s * conj s) / ((1 - s) * (1 - conj s)) by rw [hcw]; simp only [w, cay_jl]; field_simp; ring,
          show I - conj w = 2 * I / (1 - conj s) by rw [hcw]; field_simp; ring, hcs]; field_simp
      rw [ext1_of_im _ hwim.ne', ext1_of_im f' hwim.ne']
      have hqi : q1 (m + 2) iP ⟨w,
                                hwim.ne'⟩ = (((m + 2 : ℕ) : ℂ) - 1) / (4 * π) * ((w - conj w) / (I - conj w)) ^ (m + 2) := by
        unfold q1; rw [ite_eq_left (by simpa [iP] using hwim)]; rfl
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
      have hr2 : (1 - (r : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (by nlinarith : (1 - r ^ 2 : ℝ) ≠ 0)
      rw [hqi, hratio, div_pow]
      have hkey : ((4 * r / (1 - r ^ 2) ^ 2 : ℝ) : ℂ) * ((((m + 2 : ℕ) : ℂ) - 1) / (4 * π)) * (1 - (r : ℂ) ^ 2) ^ (m + 2) =
          ((((m : ℝ) + 1) / π * r * (1 - r ^ 2) ^ m : ℝ) : ℂ) := by push_cast; field_simp; ring
      rw [← hkey]; ring
    change ∫ p : ℝ × ℝ in Set.Ioo 0 1 ×ˢ Set.Ioo (-π) π, ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) * ext1 (fun w => q1 (m + 2) iP w * f' w) (cay_jl (circleMap 0 p.1 p.2)) = f' iP
    rw [setIntegral_congr_fun hS hpt, Measure.volume_eq_prod,
        setIntegral_prod _ (by rw [← Measure.volume_eq_prod]; exact hIO.congr_fun hpt hS)]
    let G (s : ℂ) := ext1 f' (cay_jl s) / (1 - s) ^ (m + 2)
    have hGd : DifferentiableOn ℂ G (ball 0 1) :=
      (hf'.comp (fun s hs => (DifferentiableAt.div (by fun_prop) (by fun_prop) (hdisc (mem_ball_zero_iff.1 hs)).1).differentiableWithinAt)
        fun s hs => (hdisc (mem_ball_zero_iff.1 hs)).2.ne').div
        (fun s _ => (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => (1 - s) ^ (m + 2)) s).differentiableWithinAt)
        fun s hs => pow_ne_zero _ (hdisc (mem_ball_zero_iff.1 hs)).1
    have hin r (hr : r ∈ Ioo (0 : ℝ) 1) :
        ∫ θ in Ioo (-π) π, ((((m : ℝ) + 1) / π * r * (1 - r ^ 2) ^ m : ℝ) : ℂ) * G (circleMap 0 r θ) =
          ((((m : ℝ) + 1) / π * r * (1 - r ^ 2) ^ m : ℝ) : ℂ) * (2 * (π : ℂ) * f' iP) := by
      rw [integral_const_mul]; congr 1
      have h1 := (show DiffContOnCl ℂ G (ball 0 |r|) by
        rw [abs_of_pos hr.1]; exact (hGd.mono (by rw [closure_ball 0 hr.1.ne']; exact closedBall_subset_ball hr.2)).diffContOnCl).circleAverage
      have hper : Periodic (fun θ => G (circleMap 0 r θ)) (2 * π) :=
          fun θ => by show G (circleMap 0 r (θ + 2 * π)) = _; rw [periodic_circleMap]
      have h2 := hper.intervalIntegral_add_eq (-π) 0; rw [show -π + 2 * π = π by ring,
                                                          zero_add] at h2
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos]),
          h2]
      rw [Real.circleAverage_def, real_smul, show G 0 = f' iP by simp [G,
                                                                       cay_jl]; exact ext1_coe f' iP] at h1
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
      rw [← h1]; push_cast; field_simp
    have hrad : ∫ r in Ioo (0 : ℝ) 1, ((m : ℝ) + 1) / π * r * (1 - r ^ 2) ^ m = 1 / (2 * π) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
      have hd x (_ : x ∈ uIcc (0 : ℝ) 1) : HasDerivAt (fun r : ℝ => -(1 - r ^ 2) ^ (m + 1) / (2 * π)) (((m : ℝ) + 1) / π * x * (1 - x ^ 2) ^ m) x :=
        ((((by simpa using (hasDerivAt_pow 2 x).const_sub 1 : HasDerivAt (fun r : ℝ => 1 - r ^ 2) (-(2 * x)) x).pow (m + 1)).neg.div_const (2 * π)).congr_deriv $ by
          have := pi_ne_zero; simp only [Nat.add_sub_cancel]; push_cast; field_simp)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((by fun_prop : Continuous fun x : ℝ => ((m : ℝ) + 1) / π * x * (1 - x ^ 2) ^ m).intervalIntegrable 0 1)]; simp; ring
    rw [setIntegral_congr_fun measurableSet_Ioo hin, integral_mul_const, integral_complex_ofReal,
        hrad]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
    push_cast; field_simp
  let e : P ≃ₜ P := ⟨MulAction.toPerm g, cont_smul_P g, cont_smul_P g⁻¹⟩
  rw [← (mp_smul_P g).integral_comp e.measurableEmbedding (fun w => q1 k (g • iP) w * f w)]
  have hpt w : q1 k (g • iP) (g • w) * f (g • w) = j1 k g iP * (q1 k iP w * f' w) := by
    have hj := j1_ne k g w
    calc _ = (q1 k (g • iP) (g • w) * j1 k g w) * f (g • w) / j1 k g w := by field_simp
      _ = (j1 k g iP * q1 k iP w) * f (g • w) / j1 k g w := by rw [q1_smul]
      _ = _ := by unfold f'; ring
  simp_rw [hpt]; rw [integral_const_mul, hat_i]; have := j1_ne k g iP; unfold f'; field_simp

-- === MultivariableReproducingFormula ===

theorem multivariable_reproducing_formula_proof_jl : B1a → B1b → B3 → KapInt → MultivariableReproducingFormula := by
  intro ha _ h3 hK I _ k hk f hf ⟨C, hC⟩ z
  have : SigmaFinite (volume : Measure P) := ha.1
  have hint {J : Type} [Fintype J] (k' : J → ℕ) (hk' : ∀ v,
                                                 4 ≤ k' v) (g : X J → ℂ) (hg : Continuous g) (C' : ℝ)
      (hC' : ∀ w, ‖g w‖ * nrm k' w ≤ C') (w0 : X J) : Integrable fun w => qq k' w0 w * g w := by
    obtain ⟨C1, _, h⟩ := hK J k' hk'; obtain ⟨hm, hl, -⟩ := h w0
    have hKi : Integrable (Kap k' w0) := ⟨hm.aestronglyMeasurable, by
      show ∫⁻ w, ‖Kap k' w0 w‖ₑ < ∞; simp_rw [Real.enorm_eq_ofReal (Kap_nonneg_jl k' w0 _)]; exact hl.trans_lt ENNReal.coe_lt_top⟩
    have hc := cst_nonneg_jl k' fun v => le_trans (by norm_num) (hk' v)
    have hqc : Continuous (qq k' w0) :=
        continuous_finsetProd _ fun v _ => (cont_q1 (k' v)).comp (continuous_const.prodMk (continuous_apply v))
    refine (hKi.const_mul (cst_jl k' * C' / nrm k' w0)).mono' (hqc.mul hg).aestronglyMeasurable (ae_of_all _ fun w => ?_)
    rw [norm_mul, div_mul_eq_mul_div, le_div_iff₀ (nrm_pos_jl k' w0)]
    calc ‖qq k' w0 w‖ * ‖g w‖ * nrm k' w0 = (‖qq k' w0 w‖ * nrm k' w0) * ‖g w‖ := by ring
      _ = cst_jl k' * Kap k' w0 w * (‖g w‖ * nrm k' w) :=
          by rw [norm_qq_jl k' (fun v => le_trans (by norm_num) (hk' v))]; ring
      _ ≤ cst_jl k' * Kap k' w0 w * C' :=
          mul_le_mul_of_nonneg_left (hC' w) (mul_nonneg hc (Kap_nonneg_jl k' _ _))
      _ = _ := by ring
  refine ⟨hint k hk f hf.1 C hC z, ?_⟩
  have hfin : ∀ (n : ℕ) (k' : Fin n → ℕ), (∀ v, 4 ≤ k' v) → ∀ g : X (Fin n) → ℂ, SepHol g →
      ∀ C', (∀ w, ‖g w‖ * nrm k' w ≤ C') → ∀ w0, ∫ w, qq k' w0 w * g w = g w0 := by
    intro n; induction n with
    | zero =>
      intro k' _ g _ _ _ w0
      rw [show (fun w => qq k' w0 w * g w) = fun _ => g w0 from funext fun w => by rw [Subsingleton.elim w w0]; simp [qq],
        show (volume : Measure (X (Fin 0))) = Measure.dirac w0 from Measure.pi_of_empty _ w0, integral_const]; simp
    | succ n ih =>
      intro k' hk' g hg C' hC' w0
      have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure P)) 0
      have hsymm (p : P × (Fin n → P)) : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm p = Fin.cons p.1 p.2 :=
        funext fun j => by induction j using Fin.cases <;> simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
      have hqqc t w : qq k' w0 (Fin.cons t w) = q1 (k' 0) (w0 0) t * qq (fun j => k' j.succ) (fun j => w0 j.succ) w := by
        simp only [qq, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have hnrmc t w : nrm k' (Fin.cons t w : X (Fin (n + 1))) = |t.1.im| ^ ((k' 0 : ℝ) / 2) * nrm (fun j => k' j.succ) w := by
        simp only [nrm, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have hG : Integrable (fun p : P × (Fin n → P) => q1 (k' 0) (w0 0) p.1 * qq (fun j => k' j.succ) (fun j => w0 j.succ) p.2 * g (Fin.cons p.1 p.2))
          ((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) :=
        ((hmp.symm.integrable_comp_emb (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm.measurableEmbedding).2
          (hint k' hk' g hg.1 C' hC' w0)).congr (ae_of_all _ fun p => by simp only [Function.comp_apply, hsymm, hqqc])
      have hin (w : Fin n → P) : ∫ t, q1 (k' 0) (w0 0) t * qq (fun j => k' j.succ) (fun j => w0 j.succ) w * g (Fin.cons t w) =
          qq (fun j => k' j.succ) (fun j => w0 j.succ) w * g (Fin.cons (w0 0) w) := by
        have hol : Hol1 fun t => g (Fin.cons t w) := by
          convert hg.2 (Fin.cons (w0 0) w) 0 using 3 with t; funext j; induction j using Fin.cases <;> simp
        have hbd : ∃ C'', ∀ t : P, ‖g (Fin.cons t w)‖ * |t.1.im| ^ ((k' 0 : ℝ) / 2) ≤ C'' :=
          ⟨C' / nrm (fun j => k' j.succ) w, fun t => by rw [le_div_iff₀ (nrm_pos_jl _ _), mul_assoc,
                                                            ← hnrmc]; exact hC' _⟩
        rw [show (fun t => q1 (k' 0) (w0 0) t * qq (fun j => k' j.succ) (fun j => w0 j.succ) w * g (Fin.cons t w)) =
          fun t => qq (fun j => k' j.succ) (fun j => w0 j.succ) w * (q1 (k' 0) (w0 0) t * g (Fin.cons t w)) from funext fun _ => by ring,
          integral_const_mul, (h3 (k' 0) (hk' 0) _ hol hbd (w0 0)).2]
      have hsep : SepHol fun w : X (Fin n) => g (Fin.cons (w0 0) w) :=
        ⟨hg.1.comp (continuous_pi fun j => by induction j using Fin.cases; simpa using continuous_const; simpa using continuous_apply _),
         fun w v => by
          convert hg.2 (Fin.cons (w0 0) w) v.succ using 3 with t; funext j
          induction j using Fin.cases with
          | zero => simp [(Fin.succ_ne_zero v).symm]
          | succ j => simp only [Fin.cons_succ, update_apply, Fin.succ_inj]; split_ifs <;> simp_all⟩
      calc ∫ w, qq k' w0 w * g w
          = ∫ p : P × (Fin n → P), q1 (k' 0) (w0 0) p.1 * qq (fun j => k' j.succ) (fun j => w0 j.succ) p.2 * g (Fin.cons p.1 p.2)
              ∂((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) :=
            (hmp.symm.integral_comp' _).symm.trans (integral_congr_ae (ae_of_all _ fun p => by simp only [hsymm, hqqc]))
        _ = ∫ w : X (Fin n), qq (fun j => k' j.succ) (fun j => w0 j.succ) w * g (Fin.cons (w0 0) w) :=
            (integral_prod_symm _ hG).trans (integral_congr_ae (ae_of_all _ hin))
        _ = g (Fin.cons (w0 0) fun j => w0 j.succ) :=
            ih _ (fun _ => hk' _) _ hsep (C' / |(w0 0).1.im| ^ ((k' 0 : ℝ) / 2))
            (fun w => by rw [le_div_iff₀ (rpow_pos_of_pos (abs_pos.2 (w0 0).2) _), mul_assoc,
                             mul_comm (nrm _ _), ← hnrmc]; exact hC' _) _
        _ = g w0 := congrArg g (Fin.cons_self_tail w0)
  let σ := Fintype.equivFin I
  let φ := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card I) => P) σ
  have hφ (w : X I) j : φ w j = w (σ.symm j) := by
    have := Equiv.piCongrLeft_apply_apply (fun _ : Fin (Fintype.card I) => P) σ w (σ.symm j)
    rw [Equiv.apply_symm_apply] at this; exact this
  have hmp : MeasurePreserving φ volume volume :=
      measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card I) => (volume : Measure P)) σ
  have hsep : SepHol fun w' : X (Fin (Fintype.card I)) => f fun i => w' (σ i) :=
    ⟨hf.1.comp (continuous_pi fun i => continuous_apply _), fun w' j => by
      convert hf.2 (fun i => w' (σ i)) (σ.symm j) using 3 with t
      funext i; simp only [update_apply, Equiv.eq_symm_apply]; split_ifs <;> rfl⟩
  have hbd w' : ‖f fun i => w' (σ i)‖ * nrm (fun j => k (σ.symm j)) w' ≤ C := by
    rw [show nrm (fun j => k (σ.symm j)) w' = nrm k fun i => w' (σ i) from Fintype.prod_equiv σ.symm _ _ fun _ => by simp]; exact hC _
  calc ∫ w, qq k z w * f w
      = ∫ w, (fun w' : X (Fin (Fintype.card I)) => qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' * f fun i => w' (σ i)) (φ w) :=
        integral_congr_ae (ae_of_all _ fun w => by
          simp only [hφ, Equiv.symm_apply_apply,
                     show qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) (φ w) = qq k z w from
            by simp only [qq, hφ]; exact Fintype.prod_equiv σ.symm _ _ fun _ => rfl])
    _ = ∫ w', qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' * f fun i => w' (σ i) :=
        hmp.integral_comp' (fun w' : Fin (Fintype.card I) → P => qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' * f fun i => w' (σ i))
    _ = f z := by rw [hfin _ _ (fun _ => hk _) _ hsep C hbd _]; simp

-- === E5: Reproducing kernel expansion ===

theorem e5_of_reproducing_formula_jl : B1b → C3 → E0a → faceMap_zero_comp_eq_one → MultivariableReproducingFormula → E5 := by
  intro _ hC3 hE0 _ hB3 F I Gf _ _ _ D hAx k hk _ b hb f hf ⟨z, x⟩
  obtain ⟨hcount, hsf, -, hpres, -, -, hborel, -⟩ := hE0 F I Gf D hAx
  have := hcount; have := hsf; have := hborel; have := hAx.cO
  have hrep_eq (ω : D.Om) (u : Gf) (hu : (u : Gf ⧸ D.H) = ω) : ∃ h : D.H, D.rep ω = u * h :=
    ⟨⟨u⁻¹ * D.rep ω, QuotientGroup.eq.1 (hu.trans (rep_spec_jl D ω).symm)⟩, by simp⟩
  have hee (h : D.H) (u : Gf) : D.ee ((h : Gf)⁻¹ * u) * (D.χ h : ℂ) = D.ee u := by
    rw [ee_inv_mul_jl, mul_comm, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
  let ω₀ : D.Om := (x : Gf ⧸ D.H)
  let a : D.Om → ℂ := ({ω₀} : Set D.Om).indicator fun _ => 1
  let h0 : D.Xs → ℂ := fun w => qq k z w * f (w, x)
  let G : D.Y → ℂ := fun y => D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1))
  have hG : G = fun y => a y.1 * h0 y.2 := funext fun y => by
    let w : X I := y.2
    change D.ee ((D.rep y.1)⁻¹ * x) * (qq k z w * f (w, D.rep y.1)) = a y.1 * h0 y.2
    by_cases hy : y.1 = ω₀
    · obtain ⟨h, hh⟩ := hrep_eq y.1 x hy.symm
      rw [show a y.1 = 1 by simp [a, hy], one_mul, hh, hf.lev,
          show (x * (h : Gf))⁻¹ * x = (h : Gf)⁻¹ by group]
      have he := hee h 1; rw [mul_one, ee_one_jl] at he
      calc _ = (D.ee (h : Gf)⁻¹ * (D.χ h : ℂ)) * h0 y.2 := by unfold h0; ring
        _ = h0 y.2 := by rw [he, one_mul]
    · have hn : (D.rep y.1)⁻¹ * x ∉ D.H :=
        fun hm => hy ((rep_spec_jl D y.1).symm.trans (QuotientGroup.eq.2 hm))
      simp [a, hy, Dat.ee, hn]
  have hB := hB3 I k hk (fun w => f (w, x)) (hf.hol x) (let ⟨C, hC⟩ := hf.bdd; ⟨C,
                                                                                fun w => hC w x⟩) z
  have hqc : Continuous (qq k z) :=
      continuous_finsetProd _ fun v _ => (cont_q1 (k v)).comp (continuous_const.prodMk (continuous_apply v))
  have hai : Integrable a Measure.count :=
    (integrable_indicator_iff MeasurableSet.of_discrete).2 ((integrableOn_singleton_iff (by simp)).2 (Or.inr (by simp)))
  have hKf (y : D.Y) : D.Kern k y (z, x) * f (y.2, D.rep y.1) = ∑' γ : PG F, G (γ • y) := by
    unfold Dat.Kern; rw [← tsum_mul_right]; refine tsum_congr fun γ => ?_
    obtain ⟨h, hh⟩ := hrep_eq (γ • y).1 (D.j γ.out * D.rep y.1) (by rw [Prod.smul_fst,
                                                                        smulO_out_jl])
    let w : X I := y.2
    have hsm : (γ • y).2 = D.act γ.out w := by rw [Prod.smul_snd, smulX_out_jl]
    change D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x) * (qq k z (D.act γ.out w) * D.J k γ.out w) * f (w, D.rep y.1) =
      D.ee ((D.rep (γ • y).1)⁻¹ * x) * (qq k z (γ • y).2 * f ((γ • y).2, D.rep (γ • y).1))
    rw [hh, hsm, hf.lev, hf.aut,
      show (D.j γ.out * D.rep y.1 * (h : Gf))⁻¹ * x = (h : Gf)⁻¹ * ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x) by group,
      ← hee h ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x)]; ring
  calc ∫ y, b y • (D.Kern k y (z, x) * f (y.2, D.rep y.1)) ∂D.μY
      = ∫ y, b y • ∑' γ : PG F, G (γ • y) ∂D.μY := by simp_rw [hKf]
    _ = ∫ y, G y ∂D.μY := (hC3 (PG F) D.Y D.μY hpres b hb G
          (by rw [hG]; exact ((measurable_const.indicator MeasurableSet.of_discrete).comp measurable_fst).mul ((hqc.mul (hf.hol x).1).measurable.comp measurable_snd))
          (by rw [hG]; exact hai.mul_prod hB.1)).2
    _ = (∫ ω, a ω ∂Measure.count) * ∫ w, h0 w := by rw [hG]; exact integral_prod_mul a h0
    _ = f (z, x) := by
        rw [show ∫ ω, a ω ∂Measure.count = 1 by
          rw [show a = ({ω₀} : Set D.Om).indicator fun _ => (1 : ℂ) from rfl,
              integral_indicator MeasurableSet.of_discrete,
            setIntegral_const, Measure.real, Measure.count_singleton, ENNReal.toReal_one, one_smul], one_mul]
        exact hB.2

-- === LinTr & E6 ===

theorem pf_LinTr_jl : LinTr := by
  intro A Y _ ν _ V _ T K ev n _ hn hK hev hKb hevb hrep
  have hbm {g h : Y → ℂ} {C D : ℝ} (hC : ∀ y, ‖g y‖ ≤ C * n y) (hD : ∀ y,
                                                                ‖h y‖ * n y ≤ D) y : ‖g y * h y‖ ≤ C * D := by
    have hC0 : 0 ≤ C :=
        by by_contra hneg; have : C * n y < 0 := mul_neg_of_neg_of_pos (not_le.1 hneg) (hn y); linarith [norm_nonneg (g y), hC y]
    rw [norm_mul]; calc ‖g y‖ * ‖h y‖ ≤ C * n y * ‖h y‖ :=
        mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _)
      _ = C * (‖h y‖ * n y) := by ring
      _ ≤ C * D := mul_le_mul_of_nonneg_left (hD y) hC0
  have hintm {g h : Y → ℂ} (hg : Measurable g) (hh : Measurable h) {C D : ℝ} (hC : ∀ y,
                                                                              ‖g y‖ ≤ C * n y) (hD : ∀ y, ‖h y‖ * n y ≤ D) :
      Integrable (fun y => g y * h y) ν :=
    (integrable_const (C * D)).mono' (hg.mul hh).aestronglyMeasurable (ae_of_all _ fun y => hbm hC hD y)
  let evl (a : A) : Module.Dual ℂ V := (LinearMap.proj a : (A → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype
  have hspan : Submodule.span ℂ (range evl) = ⊤ := by
    by_contra h
    obtain ⟨φ, hφ0, hφk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h)
    obtain ⟨v, rfl⟩ := (Module.evalEquiv ℂ V).surjective φ
    have hv : v = 0 :=
        Subtype.ext $ funext fun a => LinearMap.mem_ker.1 (hφk (Submodule.subset_span ⟨a, rfl⟩))
    exact hφ0 (by rw [hv, map_zero])
  let Good (φ : Module.Dual ℂ V) : Prop :=
    Measurable (fun y => φ (K y)) ∧ (∃ C, ∀ y,
                                     ‖φ (K y)‖ ≤ C * n y) ∧ ∀ f : V, ∫ y, φ (K y) * f.1 (ev y) ∂ν = φ f
  have hgood (φ : Module.Dual ℂ V) : Good φ := by
    let Sg : Submodule ℂ (Module.Dual ℂ V) :=
      { carrier := {ψ | Good ψ}
        zero_mem' := ⟨by simp, ⟨0, fun _ => by simp⟩, fun _ => by simp⟩
        add_mem' := fun {φ₁ φ₂} h₁ h₂ =>
          let ⟨C₁, hC₁⟩ := h₁.2.1; let ⟨C₂, hC₂⟩ := h₂.2.1
          ⟨h₁.1.add h₂.1, ⟨C₁ + C₂, fun y => by rw [LinearMap.add_apply,
                                                    add_mul]; exact (norm_add_le _ _).trans (add_le_add (hC₁ y) (hC₂ y))⟩,
           fun f => let ⟨D, hD⟩ := hevb f; by
             simp only [LinearMap.add_apply, add_mul]
             rw [integral_add (hintm h₁.1 (hev f) hC₁ hD) (hintm h₂.1 (hev f) hC₂ hD), h₁.2.2 f,
                 h₂.2.2 f]⟩
        smul_mem' := fun c ψ h => let ⟨C, hC⟩ := h.2.1
          ⟨h.1.const_mul c, ⟨‖c‖ * C, fun y => by rw [LinearMap.smul_apply, smul_eq_mul, norm_mul,
                                                      mul_assoc]; exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg c)⟩,
           fun f => by simp only [LinearMap.smul_apply, smul_eq_mul,
                                  mul_assoc]; rw [integral_const_mul, h.2.2 f]⟩ }
    have htop : Sg = ⊤ := by
      rw [eq_top_iff, ← hspan, Submodule.span_le]; rintro _ ⟨a, rfl⟩; exact ⟨hK a, hKb a,
                                                                             fun f => hrep f a⟩
    exact show φ ∈ Sg from htop.symm ▸ Submodule.mem_top
  let b := Module.finBasis ℂ V
  have hexp y : (T (K y)).1 (ev y) = ∑ i, b.coord i (K y) * (T (b i)).1 (ev y) := by
    have e : T (K y) = ∑ i, b.repr (K y) i • T (b i) :=
      (congrArg T (b.sum_repr (K y)).symm).trans $ by rw [map_sum]; exact Finset.sum_congr rfl fun _ _ => map_smul T _ _
    rw [e]; simp [Module.Basis.coord_apply]
  choose Cs hCs using fun i => (hgood (b.coord i)).2.1
  choose Ds hDs using fun i => hevb (T (b i))
  refine ⟨by simp_rw [hexp]; exact Finset.measurable_sum _ fun i _ => (hgood (b.coord i)).1.mul (hev (T (b i))),
    ⟨∑ i, Cs i * Ds i,
     fun y => by rw [hexp]; exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hbm (hCs i) (hDs i) y)⟩, ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℂ b T, Matrix.trace]; simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => hintm (hgood (b.coord i)).1 (hev (T (b i))) (hCs i) (hDs i)]
  exact Finset.sum_congr rfl fun i _ => by rw [(hgood (b.coord i)).2.2 (T (b i))]; simp [LinearMap.toMatrix_apply, Module.Basis.coord_apply]

theorem e6_of_linear_trace_identity_jl : E0a → FormsStableUnderOperators → KernelTermsInvariantBounded → E3 → E4 → faceMap_zero_comp_eq_one → E5 → LinTr → E6 := by
  intro _ _ _ hE3 hE4 hE4b hE5 _ F I Gf ι _ _ _ _ D k a hH hfd h b hb
  have hE4' := hE4 F I Gf D hH.ax k hH.four hH.compat
  have hE4b' := hE4b F I Gf D hH.ax k hH.four hH.compat
  have hbm : Measurable fun y => (b y).toNNReal := hb.meas.real_toNNReal
  let ν : Measure D.Y := D.μY.withDensity fun y => ((b y).toNNReal : ℝ≥0∞)
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity (hE3 F I Gf D hH.ax b hb).ne
  have hint (g : D.Y → ℂ) : ∫ y, g y ∂ν = ∫ y, b y • g y ∂D.μY :=
    (integral_withDensity_eq_integral_smul hbm _).trans $ integral_congr_ae $ ae_of_all _ fun y => by simp [NNReal.smul_def, coe_toNNReal _ (hb.nonneg y)]
  let K : D.Y → D.M k := fun y => ⟨D.Kern k y, (isForm_sub D k _).2 (hE4' y)⟩
  have hn_meas : Measurable fun y : D.Y => nrm k y.2 := by
    unfold nrm
    refine Finset.measurable_prod _ fun v _ => ?_
    have h1 : Measurable fun y : D.Y => |(y.2 v).1.im| :=
      continuous_abs.measurable.comp (measurable_im.comp (measurable_subtype_coe.comp ((measurable_pi_apply v).comp measurable_snd)))
    exact h1.pow_const _
  obtain ⟨hmeas, ⟨C, hC⟩, htr⟩ := pf_LinTr_jl (X I × Gf) D.Y ν (D.M k) ((Dat.Op a).restrict h) K
    (fun y => (y.2, D.rep y.1)) (fun y => nrm k y.2) hn_meas (fun y => nrm_pos_jl k y.2)
    (fun p => (hE4b' p).2.1)
    (fun f => have := hH.ax.cO; measurable_from_prod_countable_right fun ω => (((isForm_sub D k _).1 f.2).hol (D.rep ω)).1.measurable)
    (fun p => (hE4b' p).2.2)
    (fun f => let ⟨C, hC⟩ := ((isForm_sub D k _).1 f.2).bdd; ⟨C, fun y => hC _ _⟩)
    (fun f p => (hint _).trans (hE5 F I Gf D hH.ax k hH.four hH.compat b hb f.1 ((isForm_sub D k _).1 f.2) p))
  have hval (y : D.Y) : ((Dat.Op a).restrict h (K y)).1 (y.2,
                                                         D.rep y.1) = ∑' γ : PG F, D.kk k a γ y := by
    show ∑ i, D.Kern k y (y.2, D.rep y.1 * a i) = ∑' γ : PG F, D.kk k a γ y
    simp only [Dat.Kern, Dat.kk, Dat.kt, Dat.Te]
    rw [← Summable.tsum_finsetSum fun i _ => ((hE4b' (y.2, D.rep y.1 * a i)).1 y).of_norm]
    exact tsum_congr fun γ => by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by simp only [mul_assoc]
  have hgi : Integrable (fun y => ∑' γ : PG F, D.kk k a γ y) ν :=
    (integrable_const C).mono' (show Measurable fun y => ∑' γ : PG F,
                                D.kk k a γ y by simpa only [hval] using hmeas).aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [hval] using hC y)
  refine ⟨((integrable_withDensity_iff_integrable_smul hbm).1 hgi).congr (ae_of_all _ fun y => by simp [NNReal.smul_def, coe_toNNReal _ (hb.nonneg y)]),
    by rw [htr, hint]; exact integral_congr_ae (ae_of_all _ fun y => by simp only [hval])⟩

-- === C1 & C4: Action integral swap & counting measure invariance ===

theorem action_integral_swap_proof_jl : C1 := by
  intro G Y _ _ _ _ μ hP b b' hb hb'
  have hls (b1 b2 : Y → ℝ) (hb1 : IsCut G b1) (hb2 : IsCut G b2) (u : Y → ℝ≥0∞) (hu : Measurable u) :
      ∫⁻ y, oR (b1 y) * u y ∂μ = ∑' g : G, ∫⁻ y, oR (b2 (g • y)) * (oR (b1 y) * u y) ∂μ := by
    have hm g : Measurable fun y => oR (b2 (g • y)) * (oR (b1 y) * u y) :=
      (hb2.meas.comp (hP g).measurable).ennreal_ofReal.mul (hb1.meas.ennreal_ofReal.mul hu)
    rw [← lintegral_tsum fun g => (hm g).aemeasurable]
    exact lintegral_congr fun y => by
      rw [ENNReal.tsum_mul_right,
          ← ENNReal.ofReal_tsum_of_nonneg (fun _ => hb2.nonneg _) (hb2.sum y).summable,
        (hb2.sum y).tsum_eq, ENNReal.ofReal_one, one_mul]
  have hle (u : Y → ℝ≥0∞) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y) :
      ∫⁻ y, oR (b y) * u y ∂μ = ∫⁻ y, oR (b' y) * u y ∂μ := by
    rw [hls b b' hb hb' u hu, hls b' b hb' hb u hu]
    calc _ = ∑' g : G, ∫⁻ y, oR (b (g⁻¹ • y)) * (oR (b' y) * u y) ∂μ := tsum_congr fun g => by
              rw [← (hP g⁻¹).lintegral_comp_emb (actEquiv_jl hP g⁻¹).measurableEmbedding]
              exact lintegral_congr fun y => by simp [hinv]; ring
      _ = _ := (Equiv.inv G).tsum_eq fun g => ∫⁻ y, oR (b (g • y)) * (oR (b' y) * u y) ∂μ
  refine ⟨hle, fun u hu hinv hi => ?_⟩
  have hne (c : ℝ) (hc : 0 ≤ c) (v : ℂ) : ‖c • v‖ₑ = oR c * ‖v‖ₑ := by rw [enorm_smul,
                                                                           Real.enorm_eq_ofReal hc]
  have hi' : Integrable (fun y => b' y • u y) μ :=
    ⟨(hb'.meas.smul hu).aestronglyMeasurable, by
      have h := hi.hasFiniteIntegral; simp only [HasFiniteIntegral, hne _ (hb.nonneg _),
                                                 hne _ (hb'.nonneg _)] at h ⊢
      rwa [← hle _ hu.enorm fun g y => by simp [hinv]]⟩
  have his (b1 b2 : Y → ℝ) (hb1 : IsCut G b1) (hb2 : IsCut G b2) (hI : Integrable (fun y => b1 y • u y) μ) :
      ∫ y, b1 y • u y ∂μ = ∑' g : G, ∫ y, b2 (g • y) • (b1 y • u y) ∂μ := by
    have hm g : Measurable fun y => b2 (g • y) • (b1 y • u y) :=
        (hb2.meas.comp (hP g).measurable).smul (hb1.meas.smul hu)
    rw [← integral_tsum (fun g => (hm g).aestronglyMeasurable)]
    · exact integral_congr_ae (ae_of_all _ fun y => by dsimp only; rw [(hb2.sum y).summable.tsum_smul_const, (hb2.sum y).tsum_eq, one_smul])
    · have h := hI.hasFiniteIntegral; have e := hls b1 b2 hb1 hb2 (fun y => ‖u y‖ₑ) hu.enorm
      simp only [HasFiniteIntegral, hne _ (hb1.nonneg _),
                 hne _ (hb2.nonneg _)] at h e ⊢; rw [← e]; exact h.ne
  refine ⟨hi', ?_⟩
  rw [his b b' hb hb' hi, his b' b hb' hb hi']
  calc _ = ∑' g : G, ∫ y, b (g⁻¹ • y) • (b' y • u y) ∂μ := tsum_congr fun g => by
            rw [← (hP g⁻¹).integral_comp (actEquiv_jl hP g⁻¹).measurableEmbedding]
            exact integral_congr_ae (ae_of_all _ fun y => by simp [hinv]; ring)
    _ = _ := (Equiv.inv G).tsum_eq fun g => ∫ y, b (g • y) • (b' y • u y) ∂μ

theorem counting_measure_invariance_proof_jl : C1 → C4 := by
  intro _ G Ω X _ _ _ _ _ _ _ _ μ _ hμ b hb u hu hinv hint R hR β hβ
  have hP : Pres G ((Measure.count : Measure Ω).prod μ) :=
      fun g => (count_pres_jl (g • ·) (MulAction.bijective g)).prod (hμ g)
  let cut (p : Ω × X) : ℝ := if p.1 ∈ R then β p.1 p.2 else 0
  have hcut : IsCut G cut :=
      ⟨measurable_from_prod_countable_right fun ω => by by_cases h : ω ∈ R; simpa [cut,
                                                                                   h] using (hβ ω h).meas; simp [cut, h],
    fun ⟨ω, x⟩ => by dsimp only [cut]; split_ifs with h; exact (hβ _ h).nonneg x; exact le_rfl,
    fun ⟨ω, x⟩ => by
      obtain ⟨r, ⟨hrR, g₀, hg₀⟩, huniq⟩ := hR ω; dsimp only at hg₀
      let e : stabilizer G r → G := fun s => (s : G) * g₀
      have he : Injective e := fun _ _ h => Subtype.ext (mul_right_cancel h)
      rw [← he.hasSum_iff]
      · convert (hβ r hrR).sum (g₀ • x) using 1; funext s
        have h2 : ((s : G) * g₀) • ω = r := by rw [mul_smul, hg₀, s.2]
        simp [e, cut, h2, hrR, mul_smul, Subgroup.smul_def]
      · intro g hg; simp only [cut, Prod.smul_mk]; rw [ite_eq_right]
        intro hgR; apply hg
        exact ⟨⟨g * g₀⁻¹, by rw [mem_stabilizer_iff, mul_smul, ← hg₀, inv_smul_smul, huniq _ ⟨hgR,
                                                                                              mem_orbit ω g⟩, hg₀]⟩, by simp [e]⟩⟩
  obtain ⟨hI', hE⟩ := (action_integral_swap_proof_jl G (Ω × X) _ hP b cut hb hcut).2 u hu hinv hint
  have hsec := hI'.prod_right_ae; rw [Measure.ae_count_iff] at hsec
  have hF := hI'.integral_prod_left
  have hsum : HasSum (fun ω => ∫ x, cut (ω, x) • u (ω, x) ∂μ) (∫ y,
                                                               b y • u y ∂(Measure.count.prod μ)) := by
    rw [hE, integral_prod _ hI', integral_countable hF]; simp only [count_real_singleton, one_smul]
    exact (integrable_count_iff.1 hF).of_norm.hasSum
  refine ⟨fun r hr => by simpa [cut, hr] using hsec r, ?_⟩
  rw [← hasSum_subtype_iff_of_support_subset (s := R) (fun ω hω => by by_contra h; exact hω (by simp [cut, h]))] at hsum
  convert hsum using 1; funext r; simp [cut, r.2]

-- === E1: Kernel series converges ===

theorem kernel_series_converges_proof_jl : B1b → KernelTermsInvariantBounded → E0d → Pack → Mult → KapInt → E1 := by
  intro _ _ _ hPack hMult hKI F I Gf ι _ _ _ _ D k a hyp c₀ hc₀
  set CE : ℝ := Fintype.card ι * cst_jl k
  obtain ⟨Cp, hCp⟩ := hPack F I Gf D hyp.ax
  obtain ⟨CM, hCM⟩ := hMult F I Gf D hyp.ax (1 / 16) c₀ (by norm_num) hc₀
  obtain ⟨CK, A, hK⟩ := hKI I k hyp.four
  choose Cm hCm using fun i => hyp.ax.mul (a i)⁻¹
  set C' : ℝ := ∑ i, max (Cm i) 0
  have hC'0 : 0 ≤ C' := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hNpos (z : X I) : 0 < ∏ v, |(z v).1.im| := Finset.prod_pos fun v _ => abs_pos.2 (z v).2
  have hmain (y : D.Y) (hy : c₀ ≤ D.HtY ![0, 1] y) :
      ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 y‖ₑ ≤
        ((Fintype.card ι : ℝ≥0) * Cp * A * CK * toNNReal (max CE 0 * √C' * max CM 0 * (1 + 1 / c₀)) : ℝ≥0) := by
    set Ht := D.HtY ![0, 1] y
    have hHt : 0 < Ht := hc₀.trans_le hy
    let h (w : D.Xs) : ℝ≥0∞ := oR (Kap k y.2 w * ∏ v,
                                   (|(y.2 v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2))
    set K : ℝ := max CE 0 * √C' / Ht
    have hK0 : 0 ≤ K := by positivity
    let Si i := {γ' : PG F | γ' • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
    have hpt (γ : {γ : PG F // ¬ Fix ![0,
                                       1] γ}) : ‖D.kk k a γ.1 y‖ₑ ≤ ∑ i, (Si i).indicator (fun γ' => oR K * h (γ' • y.2)) γ.1 := by
      by_cases h0 : D.Te a γ.1.out (D.rep y.1) = 0
      · simp [Dat.kk, Dat.kt, h0]
      obtain ⟨i, hi⟩ := kk_supp D a γ.1 y.1 h0
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => (Si j).indicator (fun γ' => oR K * h (γ' • y.2)) γ.1) (fun _ _ => bot_le) (Finset.mem_univ i))
      rw [indicator_of_mem (show γ.1 ∈ Si i from hi)]
      refine (ofReal_norm _).symm.trans_le ((ENNReal.ofReal_le_ofReal ?_).trans_eq (ENNReal.ofReal_mul hK0))
      have hγ' : γ.1.out 1 0 ≠ 0 := fun h0 => γ.2 ⟨γ.1.out 1 1,
                                                   funext fun j => by fin_cases j <;> simp [vecMul,
                                                                                            dotProduct, Fin.sum_univ_two, h0]⟩
      have hgy : D.HtY ![0, 1] (γ.1 • y) = (∏ v, |((γ.1 • y.2 : D.Xs) v).1.im|) * D.hf ![0,
                                                                                         1] (D.rep y.1 * a i) := by
        have e0 : D.HtY ![0, 1] (γ.1 • y) = D.Ht ![0, 1] (γ.1 • y.2) (D.rep y.1 * a i) :=
          (congrArg (D.HtY ![0,
                             1]) (Prod.ext hi rfl : γ.1 • y = ((((D.rep y.1 * a i : Gf) : Gf ⧸ D.H) : D.Om), γ.1 • y.2))).trans
            (htY_mk_jl D hyp.ax _ e01_ne (γ.1 • y.2) (D.rep y.1 * a i))
        rw [e0]; simp [Dat.Ht]
      have hprod : D.HtY ![0, 1] (γ.1 • y) * Ht ≤ 1 := by
        have := htY_smul_jl D hyp.ax ![0, 1] e01_ne γ.1.out y; rw [QuotientGroup.out_eq'] at this
        rw [this, mul_comm]; exact htY_prod_jl D hyp.ax _ _ (by simpa [vecMul, dotProduct,
                                                                       Fin.sum_univ_two] using hγ') y
      have hmul : D.hf ![0, 1] (D.rep y.1) ≤ Cm i * D.hf ![0,
                                                           1] (D.rep y.1 * a i) := by simpa using hCm i _ e01_ne (D.rep y.1 * a i)
      have hCm0 : 0 ≤ Cm i := by have := hyp.ax.pos ![0,
                                                      1] e01_ne (D.rep y.1); have := hyp.ax.pos ![0,
                                                                                                  1] e01_ne (D.rep y.1 * a i); nlinarith
      have hCi : Cm i ≤ C' :=
          (le_max_left _ _).trans (Finset.single_le_sum (f := fun j => max (Cm j) 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ i))
      have hrat : (∏ v, |((γ.1 • y.2 : D.Xs) v).1.im|) * Ht ^ 2 ≤ C' * ∏ v, |(y.2 v).1.im| := by
        have hy0 : Ht = (∏ v, |(y.2 v).1.im|) * D.hf ![0, 1] (D.rep y.1) := by simp [Ht, Dat.HtY,
                                                                                     Dat.Ht]
        have hNg : 0 ≤ ∏ v, |((γ.1 • y.2 : D.Xs) v).1.im| :=
            Finset.prod_nonneg fun _ _ => abs_nonneg _
        have e2 : (∏ v, |((γ.1 • y.2 : D.Xs) v).1.im|) * D.hf ![0,
                                                                1] (D.rep y.1) ≤ Cm i * D.HtY ![0,
                                                                                                1] (γ.1 • y) := by
          rw [hgy]; nlinarith [mul_le_mul_of_nonneg_left hmul hNg]
        calc _ = ((∏ v, |((γ.1 • y.2 : D.Xs) v).1.im|) * D.hf ![0,
                                                                1] (D.rep y.1)) * Ht * ∏ v, |(y.2 v).1.im| := by rw [sq, hy0]; ring
          _ ≤ (Cm i * D.HtY ![0,
                              1] (γ.1 • y)) * Ht * ∏ v, |(y.2 v).1.im| := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e2 hHt.le) (hNpos y.2).le
          _ = Cm i * (D.HtY ![0, 1] (γ.1 • y) * Ht) * ∏ v, |(y.2 v).1.im| := by ring
          _ ≤ Cm i * 1 * ∏ v, |(y.2 v).1.im| :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hCm0) (hNpos y.2).le
          _ ≤ C' * ∏ v, |(y.2 v).1.im| :=
              by rw [mul_one]; exact mul_le_mul_of_nonneg_right hCi (hNpos y.2).le
      have hsq : ((∏ v, |((γ.1 • y.2 : D.Xs) v).1.im|) / ∏ v,
                  |(y.2 v).1.im|) ^ ((1 : ℝ) / 2) ≤ √C' / Ht := by
        rw [← sqrt_eq_rpow]
        have hq : (∏ v, |((γ.1 • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im| ≤ C' / Ht ^ 2 :=
          (div_le_div_iff₀ (hNpos y.2) (pow_pos hHt 2)).2 hrat
        exact (sqrt_le_sqrt hq).trans_eq (by rw [sqrt_div' _ (sq_nonneg Ht), sqrt_sq hHt.le])
      have hks : Kap k y.2 (γ.1 • y.2 : D.Xs) = (Kap k y.2 (γ.1 • y.2) * ∏ v,
                                                 (|(y.2 v).1.im| / |((γ.1 • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2)) *
          ((∏ v, |((γ.1 • y.2 : D.Xs) v).1.im|) / ∏ v, |(y.2 v).1.im|) ^ ((1 : ℝ) / 2) := by
        rw [← Finset.prod_div_distrib, ← finsetProd_rpow _ _ (fun _ _ => by positivity), mul_assoc,
            ← Finset.prod_mul_distrib, Finset.prod_eq_one, mul_one]
        intro v _; have h1 := abs_pos.2 (y.2 v).2; have h2 := abs_pos.2 ((γ.1 • y.2 : D.Xs) v).2
        rw [← mul_rpow (by positivity) (by positivity),
            show |(y.2 v).1.im| / |((γ.1 • y.2 : D.Xs) v).1.im| * (|((γ.1 • y.2 : D.Xs) v).1.im| / |(y.2 v).1.im|) = 1 by field_simp, one_rpow]
      have hX : 0 ≤ Kap k y.2 (γ.1 • y.2) * ∏ v, (|(y.2 v).1.im| / |((γ.1 • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2) :=
        mul_nonneg (Kap_nonneg_jl _ _ _) (Finset.prod_nonneg fun _ _ => by positivity)
      calc ‖D.kk k a γ.1 y‖ ≤ CE * Kap k y.2 (γ.1 • y.2 : D.Xs) := norm_kk_le D k a hyp γ.1 y
        _ ≤ max CE 0 * Kap k y.2 (γ.1 • y.2 : D.Xs) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Kap_nonneg_jl _ _ _)
        _ ≤ max CE 0 * ((Kap k y.2 (γ.1 • y.2) * ∏ v,
                         (|(y.2 v).1.im| / |((γ.1 • y.2 : D.Xs) v).1.im|) ^ ((1 : ℝ) / 2)) * (√C' / Ht)) := by
              conv_lhs => rw [hks]
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hX) (le_max_right _ _)
        _ = _ := by ring
    obtain ⟨hfin, hcard⟩ := hCM y ![0, 1] e01_ne hy
    have hmeas : Measurable h := by
      have hp : Measurable fun w : D.Xs => ∏ v, (|(y.2 v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2) :=
        Finset.measurable_prod _ fun v _ => by
          have hi : Measurable fun w : D.Xs => |(w v).1.im| :=
            continuous_abs.measurable.comp (measurable_im.comp (measurable_subtype_coe.comp (measurable_pi_apply v)))
          exact (measurable_const.div hi).pow_const _
      exact ((hK y.2).1.mul hp).ennreal_ofReal
    have hA (w w' : D.Xs) (hn : Near (1 / 2) w w') : h w ≤ A * h w' :=
      (ENNReal.ofReal_le_ofReal ((hK y.2).2.2.2 w w' hn).2).trans_eq
        ((ENNReal.ofReal_mul A.2).trans (congrArg (· * h w') ENNReal.ofReal_coe_nnreal))
    have hcard' : (({γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)}.ncard : ℕ) : ℝ≥0∞) ≤ oR (max CM 0 * (1 + Ht)) := by
      rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (hcard.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
    have hfinal : oR K * oR (max CM 0 * (1 + Ht)) ≤ oR (max CE 0 * √C' * max CM 0 * (1 + 1 / c₀)) := by
      rw [← ENNReal.ofReal_mul hK0]; apply ENNReal.ofReal_le_ofReal
      have h1 : (1 + Ht) / Ht ≤ 1 + 1 / c₀ := by rw [add_div,
                                                     div_self hHt.ne']; linarith [one_div_le_one_div_of_le hc₀ hy]
      calc K * (max CM 0 * (1 + Ht)) = max CE 0 * √C' * max CM 0 * ((1 + Ht) / Ht) :=
          by simp only [K]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    calc ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 y‖ₑ
        ≤ ∑' γ : {γ : PG F // ¬ Fix ![0,
                                      1] γ}, ∑ i, (Si i).indicator (fun γ' => oR K * h (γ' • y.2)) γ.1 := ENNReal.tsum_le_tsum hpt
      _ ≤ ∑' γ : PG F, ∑ i, (Si i).indicator (fun γ' => oR K * h (γ' • y.2)) γ :=
            ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective fun γ : PG F => ∑ i, (Si i).indicator (fun γ' => oR K * h (γ' • y.2)) γ
      _ = ∑ i, ∑' γ : PG F, (Si i).indicator (fun γ' => oR K * h (γ' • y.2)) γ :=
          Summable.tsum_finsetSum fun _ _ => ENNReal.summable
      _ ≤ ∑ _i : ι, oR K * (Cp * A * oR (max CM 0 * (1 + Ht)) * CK) :=
          Finset.sum_le_sum fun i _ => by
            rw [← _root_.tsum_subtype, ENNReal.tsum_mul_left]; gcongr
            exact (hCp y _ h A hmeas hA hfin).trans (by gcongr; exact (hK y.2).2.2.1)
      _ = (Fintype.card ι : ℝ≥0∞) * Cp * A * CK * (oR K * oR (max CM 0 * (1 + Ht))) :=
          by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      _ ≤ (Fintype.card ι : ℝ≥0∞) * Cp * A * CK * oR (max CE 0 * √C' * max CM 0 * (1 + 1 / c₀)) :=
          by gcongr
      _ = _ := by rw [oR, ENNReal.ofReal]; push_cast; ring
  refine ⟨(Fintype.card ι : ℝ≥0) * Cp * A * CK * toNNReal (max CE 0 * √C' * max CM 0 * (1 + 1 / c₀)), fun y s hs hy => ?_⟩
  obtain ⟨δ, hδ⟩ := row_exists s hs
  have hfix (γ : PG F) : ¬ Fix s γ ↔ ¬ Fix ![0, 1] (MulAut.conj (δ : PG F) γ) := by
    have := fix_conj_jl ![0, 1] γ.out δ; rw [QuotientGroup.out_eq',
                                             hδ] at this; exact not_congr this.symm
  let e : {γ : PG F // ¬ Fix s γ} ≃ {γ : PG F // ¬ Fix ![0,
                                                         1] γ} := (MulAut.conj (δ : PG F)).toEquiv.subtypeEquiv hfix
  calc _ = ∑' γ : {γ : PG F // ¬ Fix s γ}, ‖D.kk k a (e γ).1 ((δ : PG F) • y)‖ₑ :=
          tsum_congr fun γ => by rw [show (e γ).1 = (δ : PG F) * γ.1 * (δ : PG F)⁻¹ from rfl,
                                     kk_conj D k a hyp]
    _ = ∑' γ : {γ : PG F // ¬ Fix ![0, 1] γ}, ‖D.kk k a γ.1 ((δ : PG F) • y)‖ₑ :=
        e.tsum_eq fun γ => ‖D.kk k a γ.1 ((δ : PG F) • y)‖ₑ
    _ ≤ _ := hmain _ (by rw [htY_smul_jl D hyp.ax _ e01_ne, hδ]; exact hy)

-- === Fsum ===

theorem pf_Fsum_jl : E0a → Fsum := by
  intro h0 F I Gf _ _ _ D hax b hb
  obtain ⟨hcG, hsig, -⟩ := h0 F I Gf D hax
  have : Countable D.Cj := hcG; have : Countable D.Om := hax.cO
  have : SigmaFinite (volume : Measure D.Xs) := hsig
  have : SFinite D.μY := by unfold Dat.μY; infer_instance
  refine ⟨⟨hb.meas.comp (measurable_fst.snd.prodMk measurable_snd), fun _ => hb.nonneg _,
           fun p => hb.sum (p.1.2, p.2)⟩, fun u hu hfin => ?_⟩
  have hgm : Measurable fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2 :=
    measurable_from_prod_countable_right fun c => hb.meas.smul (hu (D.el c))
  have hgi : Integrable (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2) (Measure.count.prod D.μY) := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    show ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY) < ∞
    have hm c : Measurable fun y : D.Y => ‖b y • u (D.el c) y‖ₑ :=
        (hb.meas.smul (hu (D.el c))).enorm
    rw [lintegral_prod _ hgm.enorm.aemeasurable, lintegral_count]
    dsimp only; rw [← lintegral_tsum fun c => (hm c).aemeasurable]
    exact (lintegral_congr fun y => by simp only [enorm_smul,
                                                  Real.enorm_of_nonneg (hb.nonneg y)]; exact ENNReal.tsum_mul_left).trans_lt hfin
  have hae : ∀ᵐ y ∂D.μY, ∫ c, b y • u (D.el c) y ∂(Measure.count : Measure D.Cj) = b y • ∑' γ, u γ y := by
    filter_upwards [hgi.prod_left_ae] with y hy
    rw [integral_countable hy]; simp only [measureReal_def, Measure.count_singleton,
                                           ENNReal.toReal_one, one_smul]; exact tsum_const_smul'' (b y)
  have hmp : MeasurePreserving (MeasurableEquiv.prodAssoc : (D.Cj × D.Om) × D.Xs ≃ᵐ D.Cj × D.Om × D.Xs) D.μC (Measure.count.prod D.μY) := by
    have hcp : (Measure.count : Measure D.Cj).prod (Measure.count : Measure D.Om) = Measure.count :=
      Measure.ext_iff_singleton.2 fun ⟨a, b⟩ => by rw [Measure.count_singleton,
                                                       ← singleton_prod_singleton, Measure.prod_prod, Measure.count_singleton, Measure.count_singleton, one_mul]
    rw [show D.μC = (Measure.count.prod Measure.count).prod volume by unfold Dat.μC; rw [hcp]]
    exact measurePreserving_prodAssoc _ _ _
  refine ⟨measurable_from_prod_countable_right fun a => by dsimp only; exact (hu (D.el a.1)).comp measurable_prodMk_left,
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hgi, hgi.integral_prod_right.congr hae,
    (integral_congr_ae hae).symm.trans $ (integral_prod_symm _ hgi).symm.trans (hmp.integral_comp' _).symm⟩

end UpperTheory.Esk

-- ==== B4

noncomputable section

open MeasureTheory Matrix Finset Filter Function Subgroup MulAction QuotientGroup Topology Metric
open Set hiding center
open Real hiding dist_eq
open _root_.Complex hiding log exp exp_add exp_neg exp_log exp_nat_mul log_mul log_exp exp_sub
open scoped ENNReal NNReal ComplexConjugate Classical Real

namespace UpperTheory.Esk

-- === Shared helpers for B4 & B5 ===

def ptE_jl : ℝ × {y : ℝ // y ≠ 0} ≃ᵐ P where
  toFun p := pt p.1 p.2.1 p.2.2
  invFun z := (z.1.re / z.1.im, ⟨z.1.im, z.2⟩)
  left_inv := fun ⟨x, y, hy⟩ => Prod.ext (by simp [pt]; field_simp) (Subtype.ext (by simp [pt]))
  right_inv z := Subtype.ext $ Complex.ext (by simp [pt]; field_simp [z.2]) (by simp [pt])
  measurable_toFun := pt_cont.measurable
  measurable_invFun :=
      ((measurable_re.comp measurable_subtype_coe).div (measurable_im.comp measurable_subtype_coe)).prodMk
    (measurable_im.comp measurable_subtype_coe).subtype_mk

def smulE_jl (g : GL2 ℝ) : P ≃ᵐ P where
  toEquiv := MulAction.toPerm g
  measurable_toFun := (cont_smul_P g).measurable
  measurable_invFun := (cont_smul_P g⁻¹).measurable

lemma diag_smul_jl {g : GL2 ℝ} (hb : g 0 1 = 0) (hc : g 1 0 = 0) (z : P) : (g • z).1 = ((g 0 0 / g 1 1 : ℝ) : ℂ) * z.1 := by
  have hd : g 1 1 ≠ 0 := fun h => g.det_ne_zero (by rw [det_eq, hb, h]; ring)
  have hd' : ((g 1 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [coe_smul]; simp only [num, den, hb, hc, ofReal_zero, zero_mul, add_zero, zero_add,
                            ofReal_div]; field_simp

-- === DiagonalIntegrandVanishes ===

theorem diagonal_integrand_vanishes_proof_jl : DiagonalIntegrandVanishes := by
  intro k hk g hb hc hne
  have hdet : g.val.det = g 0 0 * g 1 1 := by rw [det_eq, hb]; ring
  have hdet0 : g 0 0 * g 1 1 ≠ 0 := hdet ▸ g.det_ne_zero
  have hd : g 1 1 ≠ 0 := right_ne_zero_of_mul hdet0
  have hden (z : ℂ) : den g z = ((g 1 1 : ℝ) : ℂ) := by simp [den, hc]
  have him (z : P) : (g • z).1.im * z.1.im = g 0 0 * g 1 1 * (z.1.im ^ 2 / (g 1 1 * g 1 1)) := by
    rw [im_smul_jl, hden, normSq_ofReal, hdet]; ring
  rcases lt_or_gt_of_ne hdet0 with hneg | hpos
  · refine ⟨0, continuous_const, fun x y hy => ?_, integrable_zero _ _ _, by simp, by simp,
            Or.inl rfl⟩
    have : ¬(0 < (pt x y hy).1.im * (g • pt x y hy).1.im) := by
      rw [mul_comm,
          him]; nlinarith [div_nonneg (sq_nonneg (pt x y hy).1.im) (mul_self_nonneg (g 1 1))]
    simp [q1, this]
  · set r : ℝ := g 0 0 / g 1 1
    have hr0 : 0 < r :=
        by rcases lt_or_gt_of_ne hd with h | h; exact div_pos_of_neg_of_neg (by nlinarith) h; exact div_pos (by nlinarith) h
    have hr1 : 1 - r ≠ 0 := fun h => hne (by simp only [r] at h; field_simp at h; linarith)
    let D (x : ℝ) : ℂ := ((1 - r : ℝ) : ℂ) * x + ((1 + r : ℝ) : ℂ) * I
    have hDne (x : ℝ) : D x ≠ 0 := fun h => by have := congrArg im h; simp [D] at this; linarith
    have hDcont : Continuous D := by unfold D; fun_prop
    have hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖(D x ^ k)⁻¹‖ ≤ K / (1 + x ^ 2) ^ 2 := by
      set m := min ((1 - r) ^ 2) 1
      have hm0 : 0 < m := lt_min (by positivity) one_pos
      refine ⟨(m ^ 2)⁻¹, by positivity, fun x => ?_⟩
      have hsq : ‖D x‖ ^ 2 = (1 - r) ^ 2 * x ^ 2 + (1 + r) ^ 2 := by rw [Complex.sq_norm,
                                                                         normSq_apply]; simp [D]; ring
      have h1 : m * (1 + x ^ 2) ≤ ‖D x‖ ^ 2 := by
        rw [hsq]; nlinarith [mul_le_mul_of_nonneg_right (min_le_left ((1 - r) ^ 2) 1) (sq_nonneg x),
                             min_le_right ((1 - r) ^ 2) 1]
      have h1D : 1 ≤ ‖D x‖ :=
        (show 1 ≤ |(D x).im| by simp [D,
                                      abs_of_pos (by linarith : 0 < 1 + r)]; linarith).trans (abs_im_le_norm (D x))
      have h3 : (m * (1 + x ^ 2)) ^ 2 ≤ ‖D x‖ ^ k :=
        (pow_le_pow_left₀ (by positivity) h1 2).trans $ by rw [show (‖D x‖ ^ 2) ^ 2 = ‖D x‖ ^ 4 by ring]; exact pow_le_pow_right₀ h1D hk
      rw [norm_inv, norm_pow]; exact (inv_anti₀ (by positivity) h3).trans_eq (by rw [mul_pow,
                                                                                     mul_inv, div_eq_mul_inv])
    have hint_of {f : ℝ → ℂ} (hf : Continuous f) {K : ℝ} (h : ∀ x,
                                                          ‖f x‖ ≤ K / (1 + x ^ 2)) : Integrable f :=
      (integrable_inv_one_add_sq.const_mul K).mono' hf.aestronglyMeasurable (ae_of_all _ fun x => by rw [← div_eq_mul_inv]; exact h x)
    set c : ℂ := ((g 1 1 : ℝ) : ℂ) ^ k * ((|g.val.det| ^ (-(k : ℝ) / 2) : ℝ) : ℂ)
    set E : ℂ := ((k : ℂ) - 1) / (4 * π) * (2 * I * r) ^ k * c
    have hE0 : E ≠ 0 := by
      have hc0 : c ≠ 0 :=
          mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hd)) (by exact_mod_cast (rpow_pos_of_pos (abs_pos.2 g.det_ne_zero) _).ne')
      have hk1 : (k : ℂ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (by omega : k ≠ 1))
      have hpi : (4 * (π : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast pi_ne_zero)
      exact mul_ne_zero (mul_ne_zero (div_ne_zero hk1 hpi) (pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (by exact_mod_cast hr0.ne')))) hc0
    obtain ⟨K, hK, hbnd⟩ := hbound
    have hcont : Continuous fun x => E * (D x ^ k)⁻¹ :=
        continuous_const.mul ((hDcont.pow k).inv₀ fun x => pow_ne_zero _ (hDne x))
    refine ⟨fun x => E * (D x ^ k)⁻¹, hcont, fun x y hy => ?_,
      hint_of hcont fun x => by rw [norm_mul,
                                    mul_div_assoc]; exact mul_le_mul_of_nonneg_left ((hbnd x).trans (div_le_div_of_nonneg_left hK (by positivity) (by nlinarith [sq_nonneg x]))) (norm_nonneg E),
      ?_, ?_, Or.inr fun x => mul_ne_zero hE0 (inv_ne_zero (pow_ne_zero _ (hDne x)))⟩
    · have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
      have hw : (g • pt x y hy).1 = (r : ℂ) * ((y : ℂ) * (x + I)) := diag_smul_jl hb hc _
      have hpos' : 0 < (pt x y hy).1.im * (g • pt x y hy).1.im := by
        rw [mul_comm,
            him]; exact mul_pos hpos (div_pos (pow_pos (abs_pos.2 (pt x y hy).2) 2 |> fun h => by simpa [sq_abs] using h) (mul_self_pos.2 hd))
      have hratio : ((g • pt x y hy).1 - conj (g • pt x y hy).1) / ((pt x y hy).1 - conj (g • pt x y hy).1) = 2 * I * r / D x := by
        rw [hw]; simp only [pt, map_mul, map_add, conj_ofReal, conj_I, D]
        rw [show (r : ℂ) * (y * (x + I)) - r * (y * (x + -I)) = y * (2 * I * r) by ring,
          show (y : ℂ) * (x + I) - r * (y * (x + -I)) = y * (((1 - r : ℝ) : ℂ) * x + ((1 + r : ℝ) : ℂ) * I) by push_cast; ring,
          mul_div_mul_left _ _ hy']
      simp only [q1, ite_eq_left hpos', j1, hden, hratio, div_pow, E, c]; ring
    · have hlogc : Continuous fun x : ℝ => Real.log (1 + x ^ 2) :=
        (continuous_const.add (continuous_pow 2)).log fun x => (by positivity : (0 : ℝ) < 1 + x ^ 2).ne'
      refine hint_of ((continuous_ofReal.comp hlogc).mul hcont) (K := ‖E‖ * K) fun x => ?_
      have hl0 : 0 ≤ Real.log (1 + x ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg x])
      have hl1 : Real.log (1 + x ^ 2) ≤ 1 + x ^ 2 :=
          by linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2)]
      have hp : (0 : ℝ) < 1 + x ^ 2 := by positivity
      rw [norm_mul, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hl0]
      calc Real.log (1 + x ^ 2) * (‖E‖ * ‖(D x ^ k)⁻¹‖) ≤ (1 + x ^ 2) * (‖E‖ * (K / (1 + x ^ 2) ^ 2)) :=
            mul_le_mul hl1 (mul_le_mul_of_nonneg_left (hbnd x) (norm_nonneg E)) (by positivity) hp.le
        _ = ‖E‖ * K / (1 + x ^ 2) := by field_simp
    · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
      rw [integral_const_mul]
      have hA' : (1 : ℂ) - r ≠ 0 := by exact_mod_cast hr1
      have hn' : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have hderiv x : HasDerivAt (fun x => (-((n : ℂ) + 1) * (1 - r : ℝ))⁻¹ * (D x ^ (n + 1))⁻¹) ((D x ^ (n + 2))⁻¹) x := by
        have hD : HasDerivAt D ((1 - r : ℝ) : ℂ) x := by
          show HasDerivAt (fun x : ℝ => ((1 - r : ℝ) : ℂ) * x + ((1 + r : ℝ) : ℂ) * I) ((1 - r : ℝ) : ℂ) x
          simpa using (((hasDerivAt_id x).ofReal_comp).const_mul ((1 - r : ℝ) : ℂ)).add_const (((1 + r : ℝ) : ℂ) * I)
        refine (((hD.pow (n + 1)).fun_inv (pow_ne_zero _ (hDne x))).const_mul _).congr_deriv ?_
        have := hDne x; simp only [Pi.pow_apply, Nat.add_sub_cancel]; push_cast; field_simp; ring
      have htend {l : Filter ℝ} (hl : Tendsto (fun x : ℝ => |x|) l atTop) : Tendsto (fun x => (D x ^ (n + 1))⁻¹) l (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hDn : Tendsto (fun x => ‖D x‖) l atTop := tendsto_atTop_mono
          (fun x => (show |1 - r| * |x| ≤ |(D x).re| by simp [D,
                                                              abs_mul]).trans (abs_re_le_norm (D x))) (hl.const_mul_atTop (abs_pos.2 hr1))
        exact (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (Nat.succ_ne_zero n)).comp hDn)).congr fun _ => by simp
      have hI := integral_of_hasDerivAt_of_tendsto hderiv
        (hint_of ((hDcont.pow (n + 2)).inv₀ fun x => pow_ne_zero _ (hDne x)) fun x =>
          (hbnd x).trans (div_le_div_of_nonneg_left hK (by positivity) (by nlinarith [sq_nonneg x])))
        (by simpa using (htend tendsto_abs_atBot_atTop).const_mul (-((n : ℂ) + 1) * (1 - r : ℝ))⁻¹)
        (by simpa using (htend tendsto_abs_atTop_atTop).const_mul (-((n : ℂ) + 1) * (1 - r : ℝ))⁻¹)
      rw [hI, sub_self, mul_zero]

-- === Fcen ===

theorem pf_Fcen_jl : Fcen := by
  intro F _ γ δ htr h
  have h' : ((δ * γ * δ⁻¹ : GL2 F) : PG F) = γ := by simp [h]
  set c := (δ * γ * δ⁻¹)⁻¹ * γ
  obtain ⟨h1, h2, h3⟩ := center_entries (show c ∈ Subgroup.center (GL2 F) from QuotientGroup.eq.1 h')
  have hcv : c.val = c 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) :=
      by ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]
  have hγ : γ = (δ * γ * δ⁻¹) * c := by dsimp only [c]; group
  have htrc : ((δ * γ * δ⁻¹ : GL2 F) : Matrix (Fin 2) (Fin 2) F).trace = γ.val.trace := by
    simp only [Units.val_mul]; rw [trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
                                   Matrix.one_mul]
  have ht : c 0 0 = 1 := mul_right_cancel₀ htr $ by
    conv_rhs => rw [one_mul,
                    show γ.val = (δ * γ * δ⁻¹ : GL2 F).val * c.val from congrArg Units.val hγ, hcv,
      Matrix.mul_smul, Matrix.mul_one, trace_smul, smul_eq_mul, htrc]
  have hc1 : c = 1 := Units.ext (by rw [hcv, ht, one_smul, Units.val_one])
  rw [hc1, mul_one] at hγ; calc δ * γ = δ * γ * δ⁻¹ * δ := by group
    _ = γ * δ := by rw [← hγ]

-- === F2: Diagonal terms contribution ===

lemma diag_real_gl2 (g : GL2 ℝ) (hv : 4 * g.val.det < g.val.trace ^ 2) :
    ∃ g0 : GL2 ℝ, (g0⁻¹ * g * g0) 0 1 = 0 ∧ (g0⁻¹ * g * g0) 1 0 = 0 ∧ (g0⁻¹ * g * g0) 0 0 ≠ (g0⁻¹ * g * g0) 1 1 := by
  have diag_of (M Dm : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0) (hgM : g.val * M = M * Dm)
      (h1 : Dm 0 1 = 0) (h2 : Dm 1 0 = 0) (h3 : Dm 0 0 ≠ Dm 1 1) :
      ∃ g0 : GL2 ℝ, (g0⁻¹ * g * g0) 0 1 = 0 ∧ (g0⁻¹ * g * g0) 1 0 = 0 ∧ (g0⁻¹ * g * g0) 0 0 ≠ (g0⁻¹ * g * g0) 1 1 := by
    let g0 := GeneralLinearGroup.mkOfDetNeZero M hM
    have e : (g0⁻¹ * g * g0).val = Dm := by
      rw [Units.val_mul, Units.val_mul, mul_assoc, show g0.val = M from rfl, hgM, ← mul_assoc,
          show g0⁻¹.val * M = (g0⁻¹ * g0).val from rfl, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    exact ⟨g0, by rw [e]; exact h1, by rw [e]; exact h2, by rw [e]; exact h3⟩
  rw [det_fin_two, trace_fin_two] at hv
  by_cases hb : g 0 1 = 0
  · have hne : g 0 0 ≠ g 1 1 := fun e => by rw [e, hb] at hv; nlinarith
    exact diag_of !![g 0 0 - g 1 1, 0; g 1 0, 1] !![g 0 0, 0; 0, g 1 1]
      (by rw [det_fin_two_of]; intro e; exact hne (by linear_combination e))
      (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two,
                                                         hb] <;> ring)
      (by simp) (by simp) (by simpa using hne)
  · have hΔ : 0 < (g 0 0 + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) := by linarith
    set s := √((g 0 0 + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0))
    have hs : s ^ 2 = (g 0 0 + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0) := sq_sqrt hΔ.le
    exact diag_of !![g 0 1, g 0 1; (g 0 0 + g 1 1 + s) / 2 - g 0 0, (g 0 0 + g 1 1 - s) / 2 - g 0 0]
      !![(g 0 0 + g 1 1 + s) / 2, 0; 0, (g 0 0 + g 1 1 - s) / 2]
      (by rw [det_fin_two_of]; intro e; rcases mul_eq_zero.1 (show g 0 1 * s = 0 by linear_combination -e) with h | h; exact hb h; exact (sqrt_pos.2 hΔ).ne' h)
      (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
          first | ring1 | linear_combination (1 / 4 : ℝ) * hs | linear_combination (-1 / 4 : ℝ) * hs)
      (by simp) (by simp) (by simp; linarith [sqrt_pos.2 hΔ])

theorem diagonal_terms_contribution_proof_jl : B1a → B1b → UpperHalfPlaneMeasureCoordinates → DiagonalIntegrandVanishes → C1 → E0a → KernelTermsInvariantBounded → Ecut → Fcen → F2 := by
  intro hB1a _ _ _ _ hE0a _ hEcut _ F I Gf ι _ _ _ _ D k a hyp γ ω hTE β hβ hint
  obtain ⟨hcount, -, hpres, -, -, -, hborel, -⟩ := hE0a F I Gf D hyp.ax
  have : SigmaFinite (volume : Measure P) := hB1a.1; have : Countable (PG F) := hcount
  have : BorelSpace D.Xs := hborel; have : BorelSpace (I → P) := hborel
  have hu (z : D.Xs) : D.kk k a γ (ω, z) = D.Te a γ.out (D.rep ω) *
      ∏ i, (q1 (k i) (z i) (D.r i γ.out • z i) * j1 (k i) (D.r i γ.out) (z i)) := by
    show D.Te a γ.out (D.rep ω) * (qq k z (D.act γ.out z) * D.J k γ.out z) = _; unfold qq Dat.J; rw [← Finset.prod_mul_distrib]; rfl
  by_cases hT : D.Te a γ.out (D.rep ω) = 0
  · simp [hu, hT]
  obtain ⟨i0, hi0⟩ := kk_supp D a γ ω hT; obtain ⟨htr, htr2⟩ := kk_reg D k a hyp γ ω i0 hi0
  obtain ⟨v, hv⟩ : ∃ v, 4 * (D.r v γ.out).val.det < (D.r v γ.out).val.trace ^ 2 := by
    unfold Dat.TotEll at hTE; push Not at hTE; obtain ⟨v, hv⟩ := hTE
    exact ⟨v, by rw [r_det_jl,
                     r_tr]; exact lt_of_le_of_ne hv fun h => htr2 ((D.σ v).injective (by rw [map_pow, map_mul, map_ofNat]; exact h.symm))⟩
  obtain ⟨g0, h01, h10, hne⟩ := diag_real_gl2 (D.r v γ.out) hv
  obtain ⟨φ, -, hφeq, -, -, hφ0,
          -⟩ := diagonal_integrand_vanishes_proof_jl (k v) (hyp.four v) (g0⁻¹ * D.r v γ.out * g0) h01 h10 hne
  set S := stabilizer (PG F) ((γ, ω) : D.Cj × D.Om)
  have hSmem (δ : PG F) (hδ : δ ∈ S) : δ * γ * δ⁻¹ = γ ∧ δ • ω = ω := by
    have h := mem_stabilizer_iff.1 hδ; exact ⟨congrArg (fun p : D.Cj × D.Om => D.el p.1) h,
                                              congrArg Prod.snd h⟩
  obtain ⟨β0, hβ0⟩ := (hEcut F I Gf D hyp.ax).2 ω S fun δ hδ => (hSmem δ hδ).2
  let yco (w : P) : {y : ℝ // y ≠ 0} := ⟨(g0⁻¹ • w).1.im, (g0⁻¹ • w).2⟩
  let fpr (w : P) : P := g0 • pt 0 (yco w).1 (yco w).2
  let proj (z : D.Xs) : D.Xs := update z v (fpr (z v))
  have hdiag (δ : PG F) (hδ : δ ∈ S) : (g0⁻¹ * D.r v δ.out * g0) 0 1 = 0 ∧ (g0⁻¹ * D.r v δ.out * g0) 1 0 = 0 := by
    set M := g0⁻¹ * D.r v δ.out * g0; set D0 := g0⁻¹ * D.r v γ.out * g0
    have hcomm : D.r v δ.out * D.r v γ.out = D.r v γ.out * D.r v δ.out := by
      rw [← map_mul,
          pf_Fcen_jl F γ.out δ.out htr (by simpa [QuotientGroup.out_eq'] using (hSmem δ hδ).1), map_mul]
    have hcm : M * D0 = D0 * M := by
      simp only [M, D0, mul_assoc,
                 mul_inv_cancel_left]; rw [← mul_assoc (D.r v δ.out) (D.r v γ.out) g0, hcomm,
                                           mul_assoc]
    have a1 :=
        congrArg (fun x : GL2 ℝ => x 0 1) hcm; have a2 := congrArg (fun x : GL2 ℝ => x 1 0) hcm
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h01, h10] at a1 a2
    exact ⟨(mul_eq_zero.1 (show M 0 1 * (D0 1 1 - D0 0 0) = 0 by linear_combination a1)).resolve_right (sub_ne_zero.2 hne.symm),
      (mul_eq_zero.1 (show M 1 0 * (D0 0 0 - D0 1 1) = 0 by linear_combination a2)).resolve_right (sub_ne_zero.2 hne)⟩
  have hpeq (δ : S) (z : D.Xs) : proj (δ • z) = δ • proj z := funext fun i => by
    let z' : I → P := z
    have h1 : (δ • z : D.Xs) = D.act δ.1.out z' := smulX_out_jl D δ.1 z
    have h2 : (δ • proj z : D.Xs) = D.act δ.1.out (proj z) := smulX_out_jl D δ.1 (proj z)
    rw [h1, h2]
    change update (D.act δ.1.out z') v (fpr (D.act δ.1.out z' v)) i = D.act δ.1.out (update z' v (fpr (z' v))) i
    dsimp only [Dat.act]
    by_cases hi : i = v
    · subst hi; simp only [update_self]
      have hd := hdiag δ.1 δ.2; set m := D.r i δ.1.out; set d := g0⁻¹ * m * g0
      have hm1 : m * g0 = g0 * d := by simp only [d]; group
      dsimp only [fpr]; rw [smul_smul, hm1,
                            mul_smul]; congr 1; apply Subtype.ext; rw [diag_smul_jl hd.1 hd.2]
      have e1 : g0⁻¹ • (m • z' i) = d • (g0⁻¹ • z' i) := by rw [smul_smul,
                                                                smul_smul]; congr 1; simp only [d]; group
      show (((g0⁻¹ • (m • z' i)).1.im : ℝ) : ℂ) * ((0 : ℝ) + Complex.I) = _ * ((((g0⁻¹ • z' i).1.im : ℝ) : ℂ) * ((0 : ℝ) + Complex.I))
      rw [e1, diag_smul_jl hd.1 hd.2, im_ofReal_mul]; push_cast; ring
    · simp only [update_of_ne hi]; rfl
  have hpm : Measurable proj := measurable_pi_iff.2 fun i => by
    change Measurable fun z : I → P => update z v (fpr (z v)) i
    by_cases hi : i = v
    · subst hi; simp only [update_self]
      have h1 : Continuous fpr := (cont_smul_P g0).comp (pt_cont.comp (continuous_const.prodMk
        (Continuous.subtype_mk (continuous_im.comp (continuous_subtype_val.comp (cont_smul_P g0⁻¹))) _)))
      exact h1.measurable.comp (measurable_pi_apply i)
    · simp only [update_of_ne hi]; exact measurable_pi_apply i
  have hβ' : IsCut S (fun z : D.Xs => β0 (proj z)) :=
    ⟨hβ0.meas.comp hpm, fun _ => hβ0.nonneg _, fun z => by
      have : (fun δ : S => β0 (proj (δ • z))) = fun δ : S => β0 (δ • proj z) :=
          funext fun δ => congrArg β0 (hpeq δ z)
      show HasSum _ 1; rw [this]; exact hβ0.sum _⟩
  have hinv (δ : S) (z : D.Xs) : D.kk k a γ (ω, δ • z) = D.kk k a γ (ω, z) := by
    obtain ⟨h1, h2⟩ := hSmem δ.1 δ.2; have := kk_conj D k a hyp δ.1 γ (ω,
                                                                       z); rw [h1] at this; rw [← this, Prod.smul_mk, h2]; rfl
  obtain ⟨hint',
          heq⟩ := (action_integral_swap_proof_jl S D.Xs volume (fun δ => hpres δ.1) β (fun z : D.Xs => β0 (proj z)) hβ hβ').2
    (fun z => D.kk k a γ (ω,
                          z)) ((meas_kk D k a hyp γ).comp (measurable_const.prodMk measurable_id)) hinv hint
  rw [heq]
  let fac (i : I) (w : P) := q1 (k i) w (D.r i γ.out • w) * j1 (k i) (D.r i γ.out) w
  have hint'' : Integrable (fun z : X I => β0 (proj z) • (D.Te a γ.out (D.rep ω) * ∏ i,
                                                          fac i (z i))) :=
    hint'.congr (ae_of_all _ fun z => by dsimp only; rw [hu])
  rw [show ∫ z : D.Xs, β0 (proj z) • D.kk k a γ (ω, z) = ∫ z : X I,
      β0 (proj z) • (D.Te a γ.out (D.rep ω) * ∏ i, fac i (z i)) from
    integral_congr_ae (ae_of_all _ fun z => by dsimp only; rw [hu])]
  let E : ℝ × {y : ℝ // y ≠ 0} ≃ᵐ P := ptE_jl.trans (smulE_jl g0)
  have hE : MeasurePreserving E ((volume : Measure ℝ).prod ((Measure.comap Subtype.val volume).withDensity fun y => oR (1 / |y.1|))) volume :=
    (mp_smul_P g0).comp pt_mp
  have : SigmaFinite (Measure.comap (Subtype.val : {y : ℝ // y ≠ 0} → ℝ) volume) := sf_nz
  have hfac x (y : {y : ℝ // y ≠ 0}) : fac v (E (x, y)) = φ x := by
    set d := g0⁻¹ * D.r v γ.out * g0
    rw [← hφeq x y.1 y.2]
    have hgd : D.r v γ.out = g0 * d * g0⁻¹ := by simp only [d]; group
    have hsm : D.r v γ.out • g0 • pt x y.1 y.2 = g0 • d • pt x y.1 y.2 := by rw [hgd, mul_smul,
                                                                                 mul_smul, inv_smul_smul]
    change q1 (k v) (g0 • pt x y.1 y.2) (D.r v γ.out • g0 • pt x y.1 y.2) * j1 (k v) (D.r v γ.out) (g0 • pt x y.1 y.2) = _
    rw [hsm, hgd]; exact qj_conj (k v) g0 d (pt x y.1 y.2)
  have hfE x (y : {y : ℝ // y ≠ 0}) : fpr (E (x, y)) = E (0, y) := by
    have hy' : (yco (E (x,
                        y))).1 = y.1 := by show (g0⁻¹ • g0 • pt x y.1 y.2).1.im = y.1; rw [inv_smul_smul]; simp [pt]
    change g0 • pt 0 (yco (E (x, y))).1 _ = g0 • pt 0 y.1 y.2; congr 1; apply Subtype.ext
    show ((yco (E (x,
                   y))).1 : ℂ) * ((0 : ℝ) + Complex.I) = (y.1 : ℂ) * ((0 : ℝ) + Complex.I); rw [hy']
  let _ : Unique {i // i = v} := ⟨⟨⟨v, rfl⟩⟩, fun a => Subtype.ext a.2⟩
  let Φ : X I ≃ᵐ P × ({i // ¬i = v} → P) :=
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => P) (fun i => i = v)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique {i // i = v} P) (MeasurableEquiv.refl _))
  have hΦm : MeasurePreserving Φ volume ((volume : Measure P).prod volume) := by
    have h2 : MeasurePreserving (Prod.map (MeasurableEquiv.funUnique {i // i = v} P) id)
        ((@Measure.pi {i // i = v} (fun _ => P) (Subtype.fintype (fun i => i = v)) _ fun _ => (volume : Measure P)).prod
          (Measure.pi fun _ : {i // ¬i = v} => (volume : Measure P)))
        ((volume : Measure P).prod (Measure.pi fun _ : {i // ¬i = v} => (volume : Measure P))) := by
      convert (measurePreserving_funUnique (volume : Measure P) {i // i = v}).prod
        (MeasurePreserving.id (Measure.pi fun _ : {i // ¬i = v} => (volume : Measure P)))
    exact h2.comp (measurePreserving_piEquivPiSubtypeProd (fun _ : I => (volume : Measure P)) (fun i => i = v))
  have hΦs w r : Φ.symm (w, r) = update (Φ.symm (iP, r)) v w := Φ.injective $ by
    have h0 := Φ.apply_symm_apply (iP, r); rw [Φ.apply_symm_apply]
    exact Prod.ext (by show w = update (Φ.symm (iP, r)) v w v; rw [update_self])
      (funext fun i => by show r i = update (Φ.symm (iP,
                                                     r)) v w i.1; rw [update_of_ne i.2]; exact (congrFun (congrArg Prod.snd h0) i).symm)
  have hsymm := MeasurePreserving.symm Φ hΦm
  have hint3 : Integrable (fun p : P × ({i // ¬i = v} → P) => β0 (proj (Φ.symm p)) • (D.Te a γ.out (D.rep ω) * ∏ i, fac i (Φ.symm p i)))
      ((volume : Measure P).prod (volume : Measure ({i // ¬i = v} → P))) :=
    (hsymm.integrable_comp_emb Φ.symm.measurableEmbedding).2 hint''
  rw [← hsymm.integral_comp', integral_prod_symm _ hint3]
  refine (integral_congr_ae $ ae_of_all _ fun r => ?_).trans (integral_zero ({i // ¬i = v} → P) ℂ)
  have e1 w : β0 (proj (Φ.symm (w, r))) • (D.Te a γ.out (D.rep ω) * ∏ i, fac i (Φ.symm (w, r) i)) =
      (β0 (proj (update (Φ.symm (iP,
                                 r)) v w)) : ℂ) * (D.Te a γ.out (D.rep ω) * (fac v w * ∏ i ∈ Finset.univ.erase v, fac i (Φ.symm (iP, r) i))) := by
    rw [hΦs w r, real_smul, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), update_self,
      Finset.prod_congr rfl fun i hi => by rw [update_of_ne (ne_of_mem_erase hi)]]
  simp_rw [e1]; generalize (∏ i ∈ Finset.univ.erase v, fac i (Φ.symm (iP,
                                                                      r) i)) = K; generalize Φ.symm (iP, r) = z0
  rw [← hE.integral_comp']
  have e2 : (fun q : ℝ × {y : ℝ // y ≠ 0} => (β0 (proj (update z0 v (E q))) : ℂ) * (D.Te a γ.out (D.rep ω) * (fac v (E q) * K))) =
      fun q => (fun x : ℝ => D.Te a γ.out (D.rep ω) * K * φ x) q.1 * (fun y : {y : ℝ // y ≠ 0} => (β0 (proj (update z0 v (E (0, y)))) : ℂ)) q.2 :=
    funext fun ⟨x, y⟩ => by simp only [hfac, proj, update_idem, update_self, hfE]; ring
  refine (congrArg _ e2).trans ((integral_prod_mul (fun x : ℝ => D.Te a γ.out (D.rep ω) * K * φ x)
    (fun y : {y : ℝ // y ≠ 0} => (β0 (proj (update z0 v (E (0, y)))) : ℂ))).trans ?_)
  rw [integral_const_mul, hφ0]; simp

-- === Shared elliptic fixed-point lemma (replaces BOTH exists_fix AND fp/fix_comm!) ===

lemma ell_lower_left_ne {h : GL2 ℝ} (hh : h.val.trace ^ 2 < 4 * h.val.det) : h 1 0 ≠ 0 :=
    fun e => by
  rw [trace_fin_two, det_eq, e] at hh; nlinarith [sq_nonneg (h 0 0 - h 1 1)]

def ell_fp (h : GL2 ℝ) (hh : h.val.trace ^ 2 < 4 * h.val.det) : P :=
  let hr := ell_lower_left_ne hh
  let hd : 0 < 4 * h.val.det - h.val.trace ^ 2 := by linarith
  ⟨(((h 0 0 - h 1 1) / (2 * h 1 0) : ℝ) : ℂ) + I * ((√(4 * h.val.det - h.val.trace ^ 2) / (2 * h 1 0) : ℝ) : ℂ),
    by simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_add, zero_mul, one_mul]
       exact div_ne_zero (sqrt_pos.2 hd).ne' (mul_ne_zero two_ne_zero hr)⟩

lemma ell_fix_comm {h g : GL2 ℝ} (hh : h.val.trace ^ 2 < 4 * h.val.det) (hc : g * h = h * g) :
    g • ell_fp h hh = ell_fp h hh := by
  have hr := ell_lower_left_ne hh; have hr' : ((h 1 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have hd : 0 < 4 * h.val.det - h.val.trace ^ 2 := by linarith
  set z0 := (ell_fp h hh).1
  have hQ : ((h 1 0 : ℝ) : ℂ) * z0 ^ 2 + (((h 1 1 : ℝ) : ℂ) - h 0 0) * z0 - h 0 1 = 0 := by
    have hs : ((√(4 * h.val.det - h.val.trace ^ 2) : ℝ) : ℂ) ^ 2 = ((4 * h.val.det - h.val.trace ^ 2 : ℝ) : ℂ) := by
      rw [← ofReal_pow, sq_sqrt hd.le]
    have hD : ((4 * h.val.det - h.val.trace ^ 2 : ℝ) : ℂ) = 4 * ((h 0 0 : ℂ) * h 1 1 - h 0 1 * h 1 0) - ((h 0 0 : ℂ) + h 1 1) ^ 2 := by
      simp only [trace_fin_two, det_eq]; push_cast; ring
    have hz : 2 * ((h 1 0 : ℝ) : ℂ) * z0 = ((h 0 0 : ℂ) - h 1 1) + I * (√(4 * h.val.det - h.val.trace ^ 2) : ℝ) := by
      simp only [z0, ell_fp]; push_cast; field_simp
    have h4 : 4 * ((h 1 0 : ℝ) : ℂ) * (((h 1 0 : ℝ) : ℂ) * z0 ^ 2 + (((h 1 1 : ℝ) : ℂ) - h 0 0) * z0 - h 0 1) = 0 := by
      rw [show 4 * ((h 1 0 : ℝ) : ℂ) * (((h 1 0 : ℝ) : ℂ) * z0 ^ 2 + (((h 1 1 : ℝ) : ℂ) - h 0 0) * z0 - h 0 1) =
          (2 * ((h 1 0 : ℝ) : ℂ) * z0) ^ 2 + 2 * (((h 1 1 : ℝ) : ℂ) - h 0 0) * (2 * ((h 1 0 : ℝ) : ℂ) * z0) - 4 * ((h 1 0 : ℝ) : ℂ) * h 0 1 by ring, hz]
      linear_combination ((√(4 * h.val.det - h.val.trace ^ 2) : ℝ) : ℂ) ^ 2 * I_sq - hs - hD
    exact (mul_eq_zero.1 h4).resolve_left (mul_ne_zero (by norm_num) hr')
  have e00 : ((g 0 0 : ℝ) : ℂ) * h 0 0 + g 0 1 * h 1 0 = h 0 0 * g 0 0 + h 0 1 * g 1 0 := by
    exact_mod_cast (by simpa [Units.val_mul, Matrix.mul_apply,
                              Fin.sum_univ_two] using congrArg (fun M : GL2 ℝ => M 0 0) hc)
  have e10 : ((g 1 0 : ℝ) : ℂ) * h 0 0 + g 1 1 * h 1 0 = h 1 0 * g 0 0 + h 1 1 * g 1 0 := by
    exact_mod_cast (by simpa [Units.val_mul, Matrix.mul_apply,
                              Fin.sum_univ_two] using congrArg (fun M : GL2 ℝ => M 1 0) hc)
  apply Subtype.ext; rw [coe_smul, div_eq_iff (den_ne g (ell_fp h hh).2)]
  apply mul_left_cancel₀ hr'
  change ((h 1 0 : ℝ) : ℂ) * ((g 0 0 : ℂ) * z0 + g 0 1) = ((h 1 0 : ℝ) : ℂ) * (z0 * ((g 1 0 : ℂ) * z0 + g 1 1))
  linear_combination e00 - z0 * e10 - (g 1 0 : ℂ) * hQ

-- === B4: Radial integral formula (elliptic orbital integral) ===

lemma ch_mul_jl {R : Type*} [CommRing R] (x y : R) : ∀ n, ch (x + y) (x * y) n * (x - y) = x ^ n - y ^ n
  | 0 => by simp [ch]
  | 1 => by simp [ch]
  | n + 2 => by simp only [ch]; linear_combination (x + y) * ch_mul_jl x y (n + 1) - x * y * ch_mul_jl x y n

lemma ch_cast_jl (t d : ℝ) : ∀ n, ((ch t d n : ℝ) : ℂ) = ch (t : ℂ) (d : ℂ) n
  | 0 => by simp [ch]
  | 1 => by simp [ch]
  | n + 2 => by simp only [ch]; push_cast; rw [ch_cast_jl t d (n + 1), ch_cast_jl t d n]

lemma radial_upper_int (h22 : B2) (h6 : B6) (k : ℕ) (hk : 4 ≤ k) (m : GL2 ℝ) (a b : ℝ)
    (h00 : m 0 0 = a) (h01 : m 0 1 = b) (h10 : m 1 0 = -b) (h11 : m 1 1 = a) (hb : b ≠ 0) :
    let U : P → ℂ := fun z => if 0 < z.1.im then q1 k z (m • z) * j1 k m z else 0
    let eta : ℂ := ((a : ℂ) - b * I) / (√(a ^ 2 + b ^ 2) : ℂ)
    Integrable U ∧ ∫ z, U z = eta ^ k / (1 - eta ^ 2) := by
  intro U eta
  have hab : 0 < a ^ 2 + b ^ 2 := by positivity
  have hdetm : m.val.det = a ^ 2 + b ^ 2 := by rw [det_eq, h00, h01, h10, h11]; ring
  have hI : Integrable U := by
    obtain ⟨C, hC⟩ := h6 k hk
    have hint : Integrable fun w : P => kap iP w ^ ((k : ℝ) / 2) :=
      ⟨((cont_kap.comp (continuous_const.prodMk continuous_id)).rpow_const fun _ => Or.inr (by positivity)).aestronglyMeasurable,
       by rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => rpow_nonneg (kap_nonneg_jl _ _) _)]; exact (hC iP).1.trans_lt ENNReal.coe_lt_top⟩
    have hc0 : 0 ≤ ((k : ℝ) - 1) / (4 * π) :=
        div_nonneg (by have : (4 : ℝ) ≤ k := (by exact_mod_cast hk); linarith) (by positivity)
    have hFc : Continuous fun z : P => q1 k z (m • z) * j1 k m z :=
        ((cont_q1 k).comp (continuous_id.prodMk (cont_smul_P m))).mul (cont_j1 k m)
    refine (hint.const_mul (((k : ℝ) - 1) / (4 * π) * ((a ^ 2 + b ^ 2) / b ^ 2) ^ ((k : ℝ) / 2))).mono'
      (Measurable.ite (isOpen_lt continuous_const (continuous_im.comp continuous_subtype_val)).measurableSet hFc.measurable measurable_const).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    simp only [U]; split_ifs with hz
    · rw [norm_qj_jl k (by omega) m z, mul_assoc]; apply mul_le_mul_of_nonneg_left _ hc0
      rw [← mul_rpow (by positivity) (kap_nonneg_jl _ _)]; refine rpow_le_rpow (kap_nonneg_jl _ _) ?_ (by positivity)
      set x := z.1.re; set y := z.1.im
      have hden := den_ne m z.2; have hnd := normSq_pos.2 hden
      have hwim : (m • z).1.im = (a ^ 2 + b ^ 2) * y / normSq (den m z.1) := by rw [im_smul_jl,
                                                                                    hdetm]
      have hN : ‖z.1 - conj (m • z).1‖ ^ 2 = (b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2) / normSq (den m z.1) := by
        have hc' : conj (den m z.1) ≠ 0 := (map_ne_zero _).2 hden
        rw [show z.1 - conj (m • z).1 = (z.1 * conj (den m z.1) - conj (num m z.1)) / conj (den m z.1) by rw [coe_smul, map_div₀]; field_simp,
          Complex.sq_norm, normSq_div, normSq_conj]; congr 1
        rw [normSq_apply]; simp [num, den, h00, h01, h10, h11, x, y]; ring
      have hk1 : kap z (m • z) = 4 * (a ^ 2 + b ^ 2) * y ^ 2 / (b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2) := by
        rw [kap, ite_eq_left (mul_pos hz (by rw [hwim]; positivity)), hN, hwim]; field_simp; rfl
      have hk2 : kap iP z = 4 * y / (x ^ 2 + (1 + y) ^ 2) := by
        rw [kap, ite_eq_left (by simpa [iP, y] using hz), nsq_sub_conj]
        simp only [iP, I_im, I_re, one_mul, zero_sub, neg_sq]; rfl
      rw [hk1, hk2, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : 2 * y ≤ x ^ 2 + y ^ 2 + 1 := by nlinarith [sq_nonneg x, sq_nonneg (y - 1)]
      have key : b ^ 2 * (y * (x ^ 2 + y ^ 2 + 1) + 2 * y ^ 2) ≤ b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left (show y * (x ^ 2 + y ^ 2 + 1) + 2 * y ^ 2 ≤ (x ^ 2 + y ^ 2 + 1) ^ 2 by nlinarith) (sq_nonneg b), sq_nonneg a, sq_nonneg y]
      rw [show x ^ 2 + (1 + y) ^ 2 = (x ^ 2 + y ^ 2 + 1) + 2 * y by ring]
      nlinarith [mul_le_mul_of_nonneg_left key (by positivity : 0 ≤ 4 * (a ^ 2 + b ^ 2) * y)]
    · rw [norm_zero]; exact mul_nonneg (mul_nonneg hc0 (rpow_nonneg (by positivity) _)) (rpow_nonneg (kap_nonneg_jl _ _) _)
  refine ⟨hI, ?_⟩
  rw [(h22 U (fun z hz => ite_eq_right (not_lt.2 hz.le)) hI).2]
  have hηsq : ‖eta ^ 2‖ = 1 ∧ eta ^ 2 ≠ 1 := by
    have hs : (√(a ^ 2 + b ^ 2) : ℂ) ≠ 0 := by exact_mod_cast (sqrt_pos.2 hab).ne'
    refine ⟨by rw [norm_pow, Complex.sq_norm,
                   show eta = ((a : ℂ) - b * I) / (√(a ^ 2 + b ^ 2) : ℂ) from rfl,
                map_div₀, normSq_ofReal, mul_self_sqrt hab.le, normSq_apply]; simp; rw [← sq, ← sq,
                                                                                        div_self hab.ne'],
      fun h => by
        have h' : ((a : ℂ) - b * I) ^ 2 = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) := by
          rw [show eta = ((a : ℂ) - b * I) / (√(a ^ 2 + b ^ 2) : ℂ) from rfl, div_pow,
              div_eq_one_iff_eq (pow_ne_zero 2 hs)] at h
          rw [h, ← ofReal_pow, sq_sqrt hab.le]
        have h2 := congrArg re h'; simp [sq] at h2; exact hb (by nlinarith)⟩
  have hcay (r θ : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
      ext1 U (cay_jl (circleMap 0 r θ)) = ((k : ℂ) - 1) / (4 * π) * (eta * (1 - (r : ℂ) ^ 2) / (1 - eta ^ 2 * (r : ℂ) ^ 2)) ^ k := by
    set u := circleMap 0 r θ; set z := cay_jl u
    have hnu : ‖u‖ = r := by simp [u, abs_of_pos hr0]
    have hu1 : (1 : ℂ) - u ≠ 0 := fun h => by rw [sub_eq_zero] at h; rw [← h,
                                                                         norm_one] at hnu; linarith
    have huu : u * conj u = (r : ℂ) ^ 2 := by rw [Complex.mul_conj, normSq_eq_norm_sq,
                                                  hnu]; push_cast; ring
    have hzpos : 0 < z.im := by rw [im_cay_jl]; exact div_pos (by rw [normSq_eq_norm_sq,
                                                                      hnu]; nlinarith) (normSq_pos.2 hu1)
    have hz := hzpos.ne'; let zP : P := ⟨z, hz⟩
    have hext : ext1 U z = q1 k zP (m • zP) * j1 k m zP :=
        by rw [ext1_of_im _ hz]; exact ite_eq_left hzpos
    set s := √(a ^ 2 + b ^ 2); have hs := sqrt_pos.2 hab; have hs2 := sq_sqrt hab.le
    have hS0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hα0 : (a : ℂ) + b * I ≠ 0 := fun h => hb (by simpa using congrArg im h)
    have hden : den m z = (((a : ℂ) - b * I) - ((a : ℂ) + b * I) * u) / (1 - u) := by
      rw [eq_div_iff hu1]; unfold den; rw [h10, h11]; simp only [z,
                                                                 cay_jl]; push_cast; field_simp; ring
    have hnum : num m z = I * (((a : ℂ) - b * I) + ((a : ℂ) + b * I) * u) / (1 - u) := by
      rw [eq_div_iff hu1]; unfold num; rw [h00, h01]; simp only [z,
                                                                 cay_jl]; field_simp; linear_combination (b * (1 - u)) * I_sq
    have h1 : ((a : ℂ) - b * I) - ((a : ℂ) + b * I) * u ≠ 0 :=
        (div_ne_zero_iff.1 (hden ▸ den_ne m hz)).1
    have h2 : ((a : ℂ) + b * I) - ((a : ℂ) - b * I) * conj u ≠ 0 := fun h => h1 $ by
      have := congrArg conj h; simp at this; linear_combination this
    have hA : ((a : ℂ) + b * I) - ((a : ℂ) - b * I) * u * conj u ≠ 0 := fun h => by
      rw [mul_assoc, huu, ← ofReal_pow] at h
      have h3 := congrArg im h
      simp only [sub_im, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, add_zero,
                 zero_add, mul_one, zero_im] at h3
      rcases mul_eq_zero.1 (show b * (1 + r ^ 2) = 0 by linarith) with h4 | h4; exact hb h4; nlinarith [sq_nonneg r]
    have hw : (m • zP).1 = I * (((a : ℂ) - b * I) + ((a : ℂ) + b * I) * u) / (((a : ℂ) - b * I) - ((a : ℂ) + b * I) * u) := by
      rw [coe_smul]; change num m z / den m z = _; rw [hnum, hden, div_div_div_cancel_right₀ hu1]
    have hwb : conj (m • zP).1 = -I * (((a : ℂ) + b * I) + ((a : ℂ) - b * I) * conj u) / (((a : ℂ) + b * I) - ((a : ℂ) - b * I) * conj u) := by
      rw [hw]; simp; ring
    have hwim : 0 < (m • zP).1.im := by rw [im_smul_jl,
                                            hdetm]; exact div_pos (mul_pos hab hzpos) (normSq_pos.2 (den_ne m hz))
    have hrp : |m.val.det| ^ (-(k : ℝ) / 2) = (s ^ k)⁻¹ := by
      rw [hdetm, ← hs2, abs_of_pos (by positivity), neg_div, rpow_neg (sq_nonneg _),
          sq_rpow_half hs.le]
    have hη2 : eta ^ 2 = ((a : ℂ) - b * I) / ((a : ℂ) + b * I) := by
      rw [show eta = ((a : ℂ) - b * I) / s from rfl, div_pow,
          div_eq_div_iff (pow_ne_zero 2 hS0) hα0, ← ofReal_pow, hs2]
      push_cast; linear_combination (-((a : ℂ) - b * I) * (b : ℂ) ^ 2) * I_sq
    rw [hext]; simp only [q1, j1, hrp]; rw [ite_eq_left (mul_pos hzpos hwim)]; push_cast
    rw [show ∀ c X Y S T : ℂ,
        X * Y / S = T → c * X ^ k * (Y ^ k * (S ^ k)⁻¹) = c * T ^ k from fun c X Y S T h => by rw [← h, div_pow, mul_pow]; ring]
    · have hI := I_ne_zero
      have e1 : z - conj (m • zP).1 = 2 * I * (((a : ℂ) + b * I) - ((a : ℂ) - b * I) * u * conj u) / ((1 - u) * (((a : ℂ) + b * I) - ((a : ℂ) - b * I) * conj u)) := by
        rw [hwb]; simp only [z, cay_jl]; rw [div_sub_div _ _ hu1 h2]; congr 1; ring
      have e2 : (m • zP).1 - conj (m • zP).1 = 2 * I * ((a : ℂ) + b * I) * ((a : ℂ) - b * I) * (1 - u * conj u) /
          ((((a : ℂ) - b * I) - ((a : ℂ) + b * I) * u) * (((a : ℂ) + b * I) - ((a : ℂ) - b * I) * conj u)) := by
        rw [hwb, hw, div_sub_div _ _ h1 h2]; congr 1; ring
      have e3 : 1 - eta ^ 2 * (r : ℂ) ^ 2 = (((a : ℂ) + b * I) - ((a : ℂ) - b * I) * u * conj u) / ((a : ℂ) + b * I) := by
        rw [hη2, ← huu]; field_simp
      change ((m • zP).1 - conj (m • zP).1) / (z - conj (m • zP).1) * den m z / s = _
      rw [e1, e2, hden, e3, ← huu, show eta = ((a : ℂ) - b * I) / s from rfl]
      set p := (a : ℂ) + b * I; set q := (a : ℂ) - b * I
      have hp0 : p ≠ 0 :=
          hα0; have h1' : q - p * u ≠ 0 := h1; have h2' : p - q * conj u ≠ 0 := h2; have hA' : p - q * u * conj u ≠ 0 := hA
      field_simp [hI, hu1, h1', h2', hA', hp0, hS0]
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := measurableSet_Ioo.prod measurableSet_Ioo
  change ∫ p : ℝ × ℝ in Set.Ioo 0 1 ×ˢ Set.Ioo (-π) π, ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) * ext1 U (cay_jl (circleMap 0 p.1 p.2)) = _
  rw [setIntegral_congr_fun hS fun p hp => by rw [hcay p.1 p.2 hp.1.1 hp.1.2]]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  set ζ := eta ^ 2; have hζ := hηsq.1; have hζ1 := hηsq.2
  have hne (r : ℝ) : 1 - ζ * (r : ℂ) ^ 2 ≠ 0 := fun h => by
    have h1 : ζ * (r : ℂ) ^ 2 = 1 := by linear_combination -h
    have h2 : r ^ 2 = 1 := by have := congrArg norm h1; rw [norm_mul, hζ, one_mul, norm_pow,
                                                            norm_real, Real.norm_eq_abs, sq_abs, norm_one] at this; exact this
    exact hζ1 (by rw [show (r : ℂ) ^ 2 = 1 by exact_mod_cast h2, mul_one] at h1; exact h1)
  have e1 := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun r : ℝ => ((4 * r / (1 - r ^ 2) ^ 2 : ℝ) : ℂ) * ((((n + 2 : ℕ) : ℂ) - 1) / (4 * π) * (eta * (1 - (r : ℂ) ^ 2) / (1 - ζ * (r : ℂ) ^ 2)) ^ (n + 2)))
    (fun _ : ℝ => (1 : ℂ)) (Set.Ioo 0 1) (Set.Ioo (-π) π)
  simp only [mul_one] at e1; rw [Measure.volume_eq_prod, e1, setIntegral_const,
                                 Real.volume_real_Ioo_of_le (by linarith [pi_pos])]
  have e2 : ∫ r in Ioo (0 : ℝ) 1, ((4 * r / (1 - r ^ 2) ^ 2 : ℝ) : ℂ) *
        ((((n + 2 : ℕ) : ℂ) - 1) / (4 * π) * (eta * (1 - (r : ℂ) ^ 2) / (1 - ζ * (r : ℂ) ^ 2)) ^ (n + 2)) =
      ∫ r in Ioo (0 : ℝ) 1, ((((n + 2 : ℕ) : ℂ) - 1) / (4 * π) * eta ^ (n + 2)) *
        (4 * (r : ℂ) * (1 - (r : ℂ) ^ 2) ^ n / (1 - ζ * (r : ℂ) ^ 2) ^ (n + 2)) :=
    setIntegral_congr_fun measurableSet_Ioo fun r hr => by
      have h1 : (1 - (r : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (by nlinarith [hr.1,
                                                                          hr.2] : (1 - r ^ 2 : ℝ) ≠ 0)
      have h2 := hne r; push_cast; rw [div_pow, mul_pow]; field_simp; ring
  rw [e2, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.2 hζ1
  let G (r : ℝ) : ℂ :=
      ((((n + 2 : ℕ) : ℂ) - 1) / (4 * π) * eta ^ (n + 2)) * (2 / (((n : ℂ) + 1) * (ζ - 1))) *
    ((1 - (r : ℂ) ^ 2) / (1 - ζ * (r : ℂ) ^ 2)) ^ (n + 1)
  have hderiv x (_ : x ∈ uIcc (0 : ℝ) 1) : HasDerivAt G
      (((((n + 2 : ℕ) : ℂ) - 1) / (4 * π) * eta ^ (n + 2)) * (4 * (x : ℂ) * (1 - (x : ℂ) ^ 2) ^ n / (1 - ζ * (x : ℂ) ^ 2) ^ (n + 2))) x := by
    have h1 : HasDerivAt (fun w : ℂ => 1 - w ^ 2) (-(2 * (x : ℂ))) x :=
        by simpa using (hasDerivAt_pow 2 (x : ℂ)).const_sub 1
    have h2 : HasDerivAt (fun w : ℂ => 1 - ζ * w ^ 2) (-(ζ * (2 * (x : ℂ)))) x :=
        by simpa using ((hasDerivAt_pow 2 (x : ℂ)).const_mul ζ).const_sub 1
    refine (((h1.div h2 (hne x)).pow (n + 1)).const_mul _).comp_ofReal.congr_deriv ?_
    have := hne x; simp only [Pi.div_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
                              div_pow]; field_simp; ring
  have hcont : ContinuousOn (fun x : ℝ => ((((n + 2 : ℕ) : ℂ) - 1) / (4 * π) * eta ^ (n + 2)) *
      (4 * (x : ℂ) * (1 - (x : ℂ) ^ 2) ^ n / (1 - ζ * (x : ℂ) ^ 2) ^ (n + 2))) (uIcc 0 1) :=
    continuousOn_const.mul
      (((continuousOn_const.mul continuous_ofReal.continuousOn).mul ((continuousOn_const.sub (continuous_ofReal.continuousOn.pow 2)).pow n)).div
        ((continuousOn_const.sub (continuousOn_const.mul (continuous_ofReal.continuousOn.pow 2))).pow (n + 2))
        fun x _ => pow_ne_zero _ (hne x))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  have h1ζ : 1 - ζ ≠ 0 := sub_ne_zero.2 hζ1.symm
  simp only [G, ofReal_one, one_pow, sub_self, zero_div, zero_pow (Nat.succ_ne_zero n), mul_zero,
    ofReal_zero, zero_sub, real_smul]; push_cast; field_simp; ring

theorem radial_integral_formula_proof_jl : B1a → B1b → B1c → B2 → B6 → B4 := by
  intro _ _ _ h22 h6 k hk g hg
  let F (m : GL2 ℝ) (z : P) := q1 k z (m • z) * j1 k m z
  let U (m : GL2 ℝ) (z : P) := if 0 < z.1.im then F m z else 0
  let eta (a b : ℝ) : ℂ := ((a : ℂ) - b * I) / (√(a ^ 2 + b ^ 2) : ℂ)
  have hFconj (m h : GL2 ℝ) (z : P) : F (h⁻¹ * m * h) z = F m (h • z) := by
    have := qj_conj k h (h⁻¹ * m * h) z
    rw [show h * (h⁻¹ * m * h) * h⁻¹ = m by group,
        show h • (h⁻¹ * m * h) • z = m • h • z by rw [smul_smul, smul_smul]; congr 1; group] at this
    exact this.symm
  have hcomp (h : GL2 ℝ) (f : P → ℂ) : (Integrable (fun z => f (h • z)) ↔ Integrable f) ∧ ∫ z, f (h • z) = ∫ z, f z :=
    ⟨(mp_smul_P h).integrable_comp_emb (smulE_jl h).measurableEmbedding,
     (mp_smul_P h).integral_comp (smulE_jl h).measurableEmbedding f⟩
  have hUint := radial_upper_int h22 h6 k hk
  -- Conjugate g to rotation m fixing iP
  obtain ⟨h, -, -, hh⟩ := trans_iP (ell_fp g hg)
  set m := h⁻¹ * g * h
  have hmi : m • iP = iP := by rw [show m • iP = h⁻¹ • g • h • iP by simp [m, mul_smul], hh,
                                   ell_fix_comm hg rfl, ← hh, inv_smul_smul]
  have ⟨e11, e10⟩ : m 1 1 = m 0 0 ∧ m 1 0 = -(m 0 1) := by
    have h1 := congrArg Subtype.val hmi; rw [coe_smul, div_eq_iff (den_ne m (by simp [iP]))] at h1
    have hr := congrArg re h1; have hi := congrArg im h1; simp [num, den,
                                                                iP] at hr hi; exact ⟨by linarith,
                                                                                     by linarith⟩
  have htr : g.val.trace = m.val.trace := by
    simp only [m, Units.val_mul]; rw [trace_mul_comm, ← mul_assoc, ← Units.val_mul, mul_inv_cancel,
                                      Units.val_one, Matrix.one_mul]
  have hdt : g.val.det = m.val.det := by
    simp only [m, Units.val_mul, det_mul]; rw [mul_right_comm, ← det_mul, ← Units.val_mul,
                                               inv_mul_cancel, Units.val_one, det_one, one_mul]
  set a := m 0 0; set b := m 0 1
  have htr' : m.val.trace = 2 * a := by rw [trace_fin_two]; change a + m 1 1 = _; rw [e11]; ring
  have hdt' : m.val.det = a ^ 2 + b ^ 2 := by rw [det_eq, e11, e10]; ring
  have hb : b ≠ 0 := fun h0 => by rw [htr, hdt, htr', hdt', h0] at hg; nlinarith
  -- Split F m = U m + U (dr * m * dr) ∘ (dr • ·)
  let dr : GL2 ℝ := GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, -1] (by simp)
  have hdr2 : dr * dr = 1 :=
      GeneralLinearGroup.ext fun i j => by fin_cases i <;> fin_cases j <;> simp [dr,
                                                                                 Matrix.mul_apply, Fin.sum_univ_two]
  have hdi : dr⁻¹ = dr := inv_eq_of_mul_eq_one_right hdr2
  set m' := dr * m * dr
  have hmul_dr i j : m' i j = (!![(1 : ℝ), 0; 0, -1] * m.val * !![(1 : ℝ), 0; 0,
                                                                  -1]) i j := by simp [m', dr]
  obtain ⟨hI1, hJ1⟩ := hUint m a b rfl rfl e10 e11 hb
  obtain ⟨hI2, hJ2⟩ := hUint m' a (-b) (by rw [hmul_dr]; simp [Matrix.mul_apply, Fin.sum_univ_two,
                                                               vecMul, dotProduct]; rfl)
    (by rw [hmul_dr]; simp [Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct]; rfl)
    (by rw [hmul_dr]; simp [Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct, e10])
    (by rw [hmul_dr]; simp [Matrix.mul_apply, Fin.sum_univ_two, vecMul, dotProduct,
                            e11]) (neg_ne_zero.2 hb)
  have hsplit : F m = fun z => U m z + U m' (dr • z) := funext fun z => by
    have hdrs : (dr • z).1 = -z.1 := by rw [coe_smul]; simp [num, den, dr, div_neg]
    have hFm : F m z = F m' (dr • z) := by rw [← hFconj, hdi, show dr * m' * dr = m by simp [m',
                                                                                             ← mul_assoc, hdr2]; rw [mul_assoc, hdr2, mul_one]]
    simp only [U]; rcases lt_or_gt_of_ne z.2 with hz | hz
    · rw [ite_eq_right (not_lt.2 hz.le), ite_eq_left (by rw [hdrs, neg_im]; linarith), hFm,
          zero_add]
    · rw [ite_eq_left hz, ite_eq_right (by rw [hdrs, neg_im]; linarith), add_zero]
  -- Algebraic identity: eta a b ^ k / (1 - eta a b ^ 2) + eta a (-b) ^ k / (1 - eta a (-b) ^ 2) = - ch(2a, a^2+b^2, k-1) * (a^2+b^2)^(1-k/2)
  have hch : eta a b ^ k / (1 - eta a b ^ 2) + eta a (-b) ^ k / (1 - eta a (-b) ^ 2) =
      -((ch (2 * a) (a ^ 2 + b ^ 2) (k - 1) * (a ^ 2 + b ^ 2) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ) := by
    have hp : 0 < a ^ 2 + b ^ 2 := by positivity
    set s := √(a ^ 2 + b ^ 2); have hs :=
        sqrt_pos.2 hp; have hss := sq_sqrt hp.le; have hS : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    have hr : (a ^ 2 + b ^ 2) ^ (1 - ((n + 2 : ℕ) : ℝ) / 2) = 1 / s ^ n := by
      rw [← hss, ← rpow_natCast s 2, ← rpow_mul hs.le,
        show ((2 : ℕ) : ℝ) * (1 - ((n + 2 : ℕ) : ℝ) / 2) = -(n : ℝ) by push_cast; ring, rpow_neg hs.le, rpow_natCast, one_div]
    rw [hr, show n + 2 - 1 = n + 1 by omega]
    set x : ℂ :=
        (a : ℂ) + b * I; set y : ℂ := (a : ℂ) - b * I; set u := eta a b; set v := eta a (-b)
    have hu : u = y / s := rfl
    have hv : v = x / s := by simp [v, eta, x, s]
    have hxy : x * y = (s : ℂ) ^ 2 := by rw [← ofReal_pow,
                                             hss]; push_cast; linear_combination (-(b : ℂ) ^ 2) * I_sq
    have hu0 : u ≠ 0 := div_ne_zero (fun h0 => hb (by simpa [y] using congrArg im h0)) hS
    have hv0 : v ≠ 0 :=
        by rw [hv]; exact div_ne_zero (fun h0 => hb (by simpa [x] using congrArg im h0)) hS
    have huv : u * v = 1 := by rw [hu, hv, div_mul_div_comm,
                                   div_eq_one_iff_eq (mul_ne_zero hS hS)]; linear_combination hxy
    have hvu : v - u ≠ 0 := by
      rw [hu, hv, ← sub_div]; refine div_ne_zero ?_ hS
      rw [show x - y = 2 * b * I by simp [x,
                                          y]; ring]; exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hb)) I_ne_zero
    have key := ch_mul_jl x y (n + 1)
    rw [show x + y = ((2 * a : ℝ) : ℂ) by simp [x, y]; ring,
      show x * y = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) by rw [hxy, ← ofReal_pow, hss], ← ch_cast_jl] at key
    have hC : ((ch (2 * a) (a ^ 2 + b ^ 2) (n + 1) : ℝ) : ℂ) / (s : ℂ) ^ n * (v - u) = v ^ (n + 1) - u ^ (n + 1) := by
      rw [show x = s * v by rw [hv]; field_simp, show y = s * u by rw [hu]; field_simp, ← mul_sub,
          mul_pow, mul_pow, ← mul_sub] at key
      rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero n hS)]
      exact mul_left_cancel₀ hS (by calc (s : ℂ) * (((ch (2 * a) (a ^ 2 + b ^ 2) (n + 1) : ℝ) : ℂ) * (v - u))
            = ((ch (2 * a) (a ^ 2 + b ^ 2) (n + 1) : ℝ) : ℂ) * ((s : ℂ) * (v - u)) := by ring
          _ = (s : ℂ) ^ (n + 1) * (v ^ (n + 1) - u ^ (n + 1)) := key
          _ = (s : ℂ) * ((v ^ (n + 1) - u ^ (n + 1)) * (s : ℂ) ^ n) := by rw [pow_succ']; ring)
    have t1 : u ^ (n + 2) / (1 - u ^ 2) = u ^ (n + 1) / (v - u) := by
      rw [show 1 - u ^ 2 = u * (v - u) by linear_combination -huv, pow_succ',
          mul_div_mul_left _ _ hu0]
    have t2 : v ^ (n + 2) / (1 - v ^ 2) = v ^ (n + 1) / (u - v) := by
      rw [show 1 - v ^ 2 = v * (u - v) by linear_combination -huv, pow_succ',
          mul_div_mul_left _ _ hv0]
    rw [t1, t2]; push_cast; rw [one_div, ← div_eq_mul_inv, show u - v = -(v - u) by ring, div_neg,
                                ← sub_eq_add_neg, ← sub_div, div_eq_iff hvu]
    linear_combination hC
  obtain ⟨hc1, hc2⟩ := hcomp dr (U m'); obtain ⟨hd1, hd2⟩ := hcomp h (F g)
  have hFmI : Integrable (F m) := hsplit ▸ hI1.add (hc1.2 hI2)
  have hF' : (fun z => F g (h • z)) = F m := funext fun z => (hFconj g h z).symm
  refine ⟨hd1.1 (hF' ▸ hFmI), ?_⟩
  change ∫ z, F g z = _
  rw [htr, hdt, htr', hdt', ← hch, ← hJ1, ← hJ2, ← hd2, hF', hsplit, integral_add hI1 (hc1.2 hI2),
      hc2]

-- === F3: Elliptic terms contribution ===

theorem elliptic_terms_contribution_proof_jl : B1a → B1b → B1c → B4 → C1 → E0a → KernelTermsInvariantBounded → E0d → Mult → Fcen → F3 := by
  intro hB1a _ _ hB4 _ hE0a _ _ hMult _ F I Gf ι _ _ _ _ D k a hyp γ ω hT hTe
  have : SigmaFinite (volume : Measure P) := hB1a.1
  have htr : γ.out.val.trace ≠ 0 := let ⟨i,
                                         hi⟩ := kk_supp D a γ ω hTe; (kk_reg D k a hyp γ ω i hi).1
  have hTv v : (D.r v γ.out).val.trace ^ 2 < 4 * (D.r v γ.out).val.det := by rw [r_tr,
                                                                                 r_det_jl]; exact hT v
  let z0 : D.Xs := fun v => ell_fp (D.r v γ.out) (hTv v)
  set S := stabilizer (PG F) ((γ, ω) : D.Cj × D.Om)
  have memS (g : PG F) (hg : g ∈ S) : g * γ * g⁻¹ = γ ∧ g • ω = ω := by
    rw [mem_stabilizer_iff] at hg; exact ⟨congrArg Prod.fst hg, congrArg Prod.snd hg⟩
  have fixS (g : PG F) (hg : g ∈ S) : g • z0 = z0 := by
    have hc : g.out * γ.out = γ.out * g.out :=
        pf_Fcen_jl F γ.out g.out htr (by simpa [QuotientGroup.out_eq'] using (memS g hg).1)
    rw [smulX_out_jl]; exact funext fun v => ell_fix_comm (hTv v) (by rw [← map_mul, ← map_mul, hc])
  obtain ⟨c₀, hc₀, hmink⟩ := hyp.ax.mink; obtain ⟨s, hs, hsc⟩ := hmink z0 (D.rep ω)
  obtain ⟨C, hC⟩ := hMult F I Gf D hyp.ax 1 c₀ one_pos hc₀
  have hSF : Finite S := ((hC (ω, z0) s hs hsc).1.subset fun g hg =>
    ⟨(memS g hg).2, fun v => by show 1 ≤ kap (z0 v) ((g • z0 : D.Xs) v); rw [fixS g hg,
                                                                             kap_self]⟩).to_subtype
  refine ⟨hSF, fun β hβ => ?_⟩
  let f (v : I) (w : P) := q1 (k v) w (D.r v γ.out • w) * j1 (k v) (D.r v γ.out) w
  have hu (z : D.Xs) : D.kk k a γ (ω, z) = D.Te a γ.out (D.rep ω) * ∏ v, f v (z v) := by
    show D.Te a γ.out (D.rep ω) * (qq k z (D.act γ.out z) * D.J k γ.out z) = _; rw [Finset.prod_mul_distrib]; rfl
  have hint : Integrable (fun z : D.Xs => ∏ v, f v (z v)) :=
    Integrable.fintype_prod (f := f) (μ := fun _ => volume) fun v => (hB4 (k v) (hyp.four v) _ (hTv v)).1
  have hval : ∫ z : D.Xs, ∏ v, f v (z v) = D.orb k γ.out := by
    rw [show (∫ z : D.Xs, ∏ v, f v (z v)) = ∫ z : I → P, ∏ v,
        f v (z v) ∂(Measure.pi fun _ => volume) from rfl, integral_fintype_prod_eq_prod]
    exact Finset.prod_congr rfl fun v _ => by rw [(hB4 (k v) (hyp.four v) _ (hTv v)).2, r_tr,
                                                  r_det_jl]
  have : Fintype S := Fintype.ofFinite S
  have hcard : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos_iff.2 ⟨1⟩
  let c : ℝ := (Fintype.card S : ℝ)⁻¹
  have hcut : IsCut S (fun _ : D.Xs => c) := ⟨measurable_const, fun _ => inv_nonneg.2 hcard.le,
                                              fun _ => by
    rw [show (1 : ℝ) = ∑ _ : S, c by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
                                         mul_inv_cancel₀ hcard.ne']]; exact hasSum_fintype _⟩
  have hinv (g : S) (z : D.Xs) : D.kk k a γ (ω, g • z) = D.kk k a γ (ω, z) := by
    obtain ⟨h1, h2⟩ := memS g.1 g.2; have := kk_conj D k a hyp g.1 γ (ω, z); rw [h1,
                                                                                 show (g.1 : PG F) • ((ω, z) : D.Y) = (ω, g • z) from Prod.ext h2 rfl] at this; exact this
  have hintc : Integrable (fun z : D.Xs => c • D.kk k a γ (ω, z)) :=
    ((hint.const_mul (D.Te a γ.out (D.rep ω))).smul c).congr (ae_of_all _ fun z => by dsimp only [Pi.smul_apply]; rw [hu])
  obtain ⟨-,
          heq⟩ := (action_integral_swap_proof_jl (↥S) D.Xs volume (fun g => (hE0a F I Gf D hyp.ax).2.2.1 g.1) (fun _ => c) β hcut hβ).2
    (fun z : D.Xs => D.kk k a γ (ω,
                                 z)) ((meas_kk D k a hyp γ).comp measurable_prodMk_left) hinv hintc
  rw [← heq]; simp_rw [hu]; rw [integral_smul, integral_const_mul, hval, Nat.card_eq_fintype_card,
                                real_smul]; simp [c]

end UpperTheory.Esk

-- ==== B5

noncomputable section

open MeasureTheory Matrix Finset Filter Function Subgroup MulAction QuotientGroup Topology Metric
open Set hiding center
open Real hiding dist_eq
open _root_.Complex hiding log exp exp_add exp_neg exp_log exp_nat_mul log_mul log_exp exp_sub
open scoped ENNReal NNReal ComplexConjugate Classical Real

namespace UpperTheory.Esk

-- === Shared helpers for B5 ===

lemma no_eig_of_ell {F I : Type} [Field F] (σ : I → F →+* ℝ) (v : I) (γ : GL2 F)
    (h : σ v γ.val.trace ^ 2 < 4 * σ v γ.val.det) {s : Fin 2 → F} (hs : s ≠ 0) (c : F) : s ᵥ* γ.val ≠ c • s :=
        fun heq => by
  set M := γ.val
  have h0 : s 0 * M 0 0 + s 1 * M 1 0 = c * s 0 := by simpa [vecMul, dotProduct,
                                                             Fin.sum_univ_two] using congrFun heq 0
  have h1 : s 0 * M 0 1 + s 1 * M 1 1 = c * s 1 := by simpa [vecMul, dotProduct,
                                                             Fin.sum_univ_two] using congrFun heq 1
  have hp : c ^ 2 - (M 0 0 + M 1 1) * c + (M 0 0 * M 1 1 - M 0 1 * M 1 0) = 0 := by
    by_cases hs0 : s 0 = 0
    · have hs1 : s 1 ≠ 0 := fun h1' => hs (funext fun i => by fin_cases i <;> simp [hs0, h1'])
      exact (mul_eq_zero.1 (show s 1 * (c ^ 2 - (M 0 0 + M 1 1) * c + (M 0 0 * M 1 1 - M 0 1 * M 1 0)) = 0 by
        linear_combination (M 0 0 - c) * h1 - M 0 1 * h0)).resolve_left hs1
    · exact (mul_eq_zero.1 (show s 0 * (c ^ 2 - (M 0 0 + M 1 1) * c + (M 0 0 * M 1 1 - M 0 1 * M 1 0)) = 0 by
        linear_combination (M 1 1 - c) * h0 - M 1 0 * h1)).resolve_left hs0
  have hσ := congrArg (σ v) hp; rw [trace_fin_two, det_fin_two] at h; simp at hσ h
  nlinarith [sq_nonneg (2 * σ v c - (σ v (M 0 0) + σ v (M 1 1)))]

lemma isEll_conj_jl {F : Type} [Field F] (δ γ : PG F) : IsEll (δ * γ * δ⁻¹) ↔ IsEll γ := by
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective δ; obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
  simp only [IsEll, fix_conj_jl, fix_mk_jl]
  exact ⟨fun h s hs ⟨c, hc⟩ => h (s ᵥ* (d⁻¹ : GL2 F).val) (vecMul_ne_jl hs d⁻¹) ⟨c,
                                                                                 by simpa [vecMul_vecMul] using hc⟩,
    fun h s hs ⟨c, hc⟩ => h (s ᵥ* d.val) (vecMul_ne_jl hs d) ⟨c, hc⟩⟩

lemma orbit_reps {G α : Type} [Group G] [MulAction G α] :
    ∃ f : α → α, (∀ p, f p ∈ orbit G p) ∧ (∀ p q, q ∈ orbit G p → f q = f p) ∧
      ∀ ω, ∃! r, r ∈ range f ∧ r ∈ orbit G ω := by
  let f (p : α) := Quotient.out (Quotient.mk (orbitRel G α) p)
  have hf1 p : f p ∈ orbit G p := orbitRel_apply.1 (Quotient.mk_out p)
  have hf2 p q (h : q ∈ orbit G p) : f q = f p :=
      congrArg Quotient.out (Quotient.sound (orbitRel_apply.2 h))
  exact ⟨f, hf1, hf2, fun ω => ⟨f ω, ⟨⟨ω, rfl⟩, hf1 ω⟩, by rintro r ⟨⟨p, rfl⟩,
                                                                     hr⟩; rw [← hf2 ω (f p) hr,
                                                                              hf2 p (f p) (hf1 p)]⟩⟩

-- === F4: Imaginary part bound (finiteness of totally elliptic conjugacy classes) ===

theorem imaginary_part_bound_proof_jl : B1b → B1c → E0d → Mult → F4 := by
  intro _ _ _ _ F I Gf _ _ _ D hD a
  have : Nontrivial I := hD.two
  obtain ⟨c0, hc0, hmink⟩ := hD.mink; obtain ⟨S0, C, c, hc, hnorm⟩ := hD.normal c0 hc0
  obtain ⟨Cm, hCm⟩ := hD.mul a⁻¹
  let W : Set D.Om := (fun x : Gf => ((x : Gf ⧸ D.H) : D.Om)) '' (S0 : Set Gf)
  let T (ω : D.Om) : Set D.Om := {ω3 | ∃ h ∈ D.H, ω3 = ((D.rep ω * h * a : Gf) : Gf ⧸ D.H)}
  let Good (q : (D.Cj × D.Om) × D.Xs) : Prop :=
    D.el q.1.1 • q.2 = q.2 ∧ Sg C c q.2 ∧ q.1.2 ∈ W ∧ D.HtY ![0, 1] (q.1.2,
                                                                     q.2) ^ 2 ≤ Cm ∧ D.el q.1.1 • q.1.2 ∈ T q.1.2
  let key (q : (D.Cj × D.Om) × D.Xs) : D.Om × D.Om × (I → Bool) := (q.1.2, D.el q.1.1 • q.1.2,
                                                                    fun v => decide (0 < (q.2 v).1.im))
  have hfiber (k : D.Om × D.Om × (I → Bool)) : (Prod.fst '' {q | Good q ∧ key q = k}).Finite := by
    rcases Set.eq_empty_or_nonempty {q | Good q ∧ key q = k} with h0 | ⟨q0, hq0⟩
    · rw [h0, image_empty]; exact finite_empty
    have ⟨⟨hfix0, hsg0, _, _, _⟩, hk0⟩ := hq0
    have hhf : 0 < D.hf ![0, 1] (D.rep q0.1.2) := hD.pos _ e01_ne _
    set B : ℝ := max 1 Cm / D.hf ![0, 1] (D.rep q0.1.2); set U : ℝ := C * max 1 B
    have hbox q (hq : q ∈ {q | Good q ∧ key q = k}) : q.1.2 = q0.1.2 ∧ D.el q.1.1 • q.1.2 = D.el q0.1.1 • q0.1.2 ∧
        ∀ v, (|(q.2 v).1.re| ≤ C ∧ c ≤ |(q.2 v).1.im| ∧ |(q.2 v).1.im| ≤ U) ∧ 0 < (q0.2 v).1.im * (q.2 v).1.im := by
      obtain ⟨⟨-, hsg, -, hht, -⟩, hk⟩ := hq
      have hkk := hk.trans hk0.symm; simp only [key, Prod.mk.injEq] at hkk; obtain ⟨e1, e2,
                                                                                    e3⟩ := hkk
      refine ⟨e1, e2, fun v => ⟨⟨(hsg v).1, (hsg v).2.1, ?_⟩, ?_⟩⟩
      · have hP : (∏ u, |(q.2 u).1.im|) ≤ B := by
          rw [show D.HtY ![0, 1] (q.1.2, q.2) = (∏ u, |(q.2 u).1.im|) * D.hf ![0,
                                                                               1] (D.rep q.1.2) by simp [Dat.HtY, Dat.Ht], e1] at hht
          exact (le_div_iff₀ hhf).2 (by by_cases h1 : (∏ u, |(q.2 u).1.im|) * D.hf ![0,
                                                                                     1] (D.rep q0.1.2) ≤ 1; exact le_max_of_le_left h1; exact le_max_of_le_right (by nlinarith))
        obtain ⟨v0, hv0⟩ := Finite.exists_min fun u => |(q.2 u).1.im|
        have hC0 : 0 ≤ C := (abs_nonneg _).trans (hsg v).1
        have hm : |(q.2 v0).1.im| ≤ max 1 B := by
          by_cases hle : |(q.2 v0).1.im| ≤ 1
          · exact hle.trans (le_max_left _ _)
          · push Not at hle
            have hP' : |(q.2 v0).1.im| ^ Fintype.card I ≤ ∏ u, |(q.2 u).1.im| :=
              (Finset.prod_const _).symm.trans_le (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun u _ => hv0 u)
            exact le_max_of_le_right ((le_self_pow₀ hle.le Fintype.card_ne_zero).trans (hP'.trans hP))
        exact (hsg v).2.2 v0 |>.trans (mul_le_mul_of_nonneg_left hm hC0)
      · have hde := congrFun e3 v
        rcases lt_or_gt_of_ne (q0.2 v).2 with hx | hx <;> rcases lt_or_gt_of_ne (q.2 v).2 with hy | hy
        · exact mul_pos_of_neg_of_neg hx hy
        · simp [not_lt.2 hx.le, hy] at hde
        · simp [hx, not_lt.2 hy.le] at hde
        · exact mul_pos hx hy
    obtain ⟨v0⟩ := (inferInstance : Nonempty I)
    have hU : 0 < U := by have := ((hbox q0 hq0).2.2 v0).1; linarith [this.2.1, this.2.2]
    set δ0 : ℝ := c ^ 2 / (C ^ 2 + U ^ 2); have hδ0 : 0 < δ0 := by positivity
    obtain ⟨C', hC'⟩ := hD.count q0.1.2 (δ0 ^ 2 / 4) C c (by positivity) hc
    refine ((hC' q0.2 hsg0).1.image (fun g : PG F => ((D.el q0.1.1 * g : PG F),
                                                      q0.1.2) : PG F → D.Cj × D.Om)).subset ?_
    rintro _ ⟨q, hq, rfl⟩; obtain ⟨e1, e2, hv⟩ := hbox q hq; obtain ⟨⟨hfix, -⟩, -⟩ := hq
    refine ⟨(D.el q0.1.1)⁻¹ * D.el q.1.1, ⟨by conv_lhs => rw [mul_smul, ← e1, e2, inv_smul_smul],
                                           fun v => ?_⟩,
      by show ((D.el q0.1.1 * ((D.el q0.1.1)⁻¹ * D.el q.1.1) : PG F),
               q0.1.2) = q.1; rw [mul_inv_cancel_left, ← e1]; rfl⟩
    have hklb : δ0 ≤ kap (q0.2 v) (q.2 v) := by
      obtain ⟨⟨hzr, hzi1, hzi2⟩, _⟩ := (hbox q0 hq0).2.2 v; obtain ⟨⟨hwr, hwi1, hwi2⟩, hzw⟩ := hv v
      rw [kap, ite_eq_left hzw, nsq_sub_conj]
      have hp : c ^ 2 ≤ (q0.2 v).1.im * (q.2 v).1.im := by rw [← abs_of_pos hzw,
                                                               abs_mul]; nlinarith [mul_le_mul hzi1 hwi1 hc.le (abs_nonneg _)]
      have hzr' := abs_le.1 hzr; have hwr' := abs_le.1 hwr
      have hre : ((q0.2 v).1.re - (q.2 v).1.re) ^ 2 ≤ 4 * C ^ 2 :=
          by nlinarith [mul_nonneg (show 0 ≤ 2 * C - ((q0.2 v).1.re - (q.2 v).1.re) by linarith) (show 0 ≤ 2 * C + ((q0.2 v).1.re - (q.2 v).1.re) by linarith)]
      have him2 : ((q0.2 v).1.im + (q.2 v).1.im) ^ 2 ≤ 4 * U ^ 2 := by
        nlinarith [sq_abs (q0.2 v).1.im, sq_abs (q.2 v).1.im,
                   mul_le_mul hzi2 hzi2 (abs_nonneg _) hU.le,
          mul_le_mul hwi2 hwi2 (abs_nonneg _) hU.le, mul_le_mul hzi2 hwi2 (abs_nonneg _) hU.le]
      rw [div_le_div_iff₀ (by positivity) (by nlinarith [sq_nonneg ((q0.2 v).1.re - (q.2 v).1.re),
                                                         sq_nonneg (q0.2 v).1.im, sq_nonneg (q.2 v).1.im])]
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hre him2) (sq_nonneg c),
                 mul_le_mul_of_nonneg_right hp (by positivity : (0 : ℝ) ≤ C ^ 2 + U ^ 2)]
    have k1 : kap (q0.2 v) ((((D.el q0.1.1)⁻¹ * D.el q.1.1) • q0.2 : D.Xs) v) = kap (q0.2 v) ((D.el q.1.1 • q0.2 : D.Xs) v) := by
      have := kap_smulX D (D.el q0.1.1) q0.2 (((D.el q0.1.1)⁻¹ * D.el q.1.1) • q0.2) v
      rw [hfix0, ← mul_smul, mul_inv_cancel_left] at this; exact this.symm
    have k2 : kap (q.2 v) ((D.el q.1.1 • q0.2 : D.Xs) v) = kap (q0.2 v) (q.2 v) := by
      have := kap_smulX D (D.el q.1.1) q.2 q0.2 v; rw [hfix] at this; exact this.trans (kap_symm _ _)
    show δ0 ^ 2 / 4 ≤ kap (q0.2 v) ((((D.el q0.1.1)⁻¹ * D.el q.1.1) • q0.2 : D.Xs) v)
    rw [k1]; nlinarith [kap_tri (q0.2 v) (q.2 v) ((D.el q.1.1 • q0.2 : D.Xs) v), k2,
                        mul_le_mul hklb hklb hδ0.le (hδ0.le.trans hklb)]
  have hTf ω : (T ω).Finite := ((hD.dbl a).image fun x : Gf ⧸ D.H => (D.rep ω : Gf) • x).subset $ by
    rintro _ ⟨h, hh, rfl⟩
    exact ⟨((h * a : Gf) : Gf ⧸ D.H), ⟨h, hh, rfl⟩,
           by change ((D.rep ω * (h * a) : Gf) : Gf ⧸ D.H) = _; rw [mul_assoc]⟩
  have hW : W.Finite := S0.finite_toSet.image _
  refine ⟨Prod.fst '' {q | Good q},
          ((hW.prod ((hW.biUnion fun ω _ => hTf ω).prod finite_univ)).biUnion fun k _ => hfiber k).subset
    (by rintro _ ⟨q, hq, rfl⟩; exact mem_biUnion ⟨hq.2.2.1, mem_biUnion hq.2.2.1 hq.2.2.2.2,
                                                  mem_univ _⟩ ⟨q, ⟨hq, rfl⟩,
                                                               rfl⟩), fun γ ω hell hs => ?_⟩
  let z : D.Xs := fun v => ell_fp (D.r v γ.out) (by rw [r_tr, r_det_jl]; exact hell v)
  have hz : γ • z = z := funext fun v => by rw [smulX_out_jl]; exact ell_fix_comm (by rw [r_tr,
                                                                                          r_det_jl]; exact hell v) rfl
  obtain ⟨s, hs0, hsz⟩ := hmink z (D.rep ω); obtain ⟨g, hg⟩ := row_exists s hs0
  obtain ⟨b, -, ⟨x', hx', h, hh, hbx⟩, hsg⟩ := hnorm ((g : PG F) • z) (D.rep ((g : PG F) • ω)) (by
    change c0 ≤ D.HtY ![0, 1] ((g : PG F) • ((ω, z) : D.Y)); rw [htY_smul_jl D hD _ e01_ne,
                                                                 hg]; exact hsz)
  set δ := b * g
  have hδω : (δ : PG F) • ω = ((x' : Gf ⧸ D.H) : D.Om) := by
    rw [show (δ : PG F) = (b : PG F) * (g : PG F) from rfl, mul_smul]
    have e2 := D.mk_smulO b (D.rep ((g : PG F) • ω)); rw [rep_spec_jl] at e2; rw [e2, hbx]
    exact QuotientGroup.eq.2 (by simpa using inv_mem hh)
  have hfixδ : ((δ : PG F) * γ * (δ : PG F)⁻¹) • ((δ : PG F) • z) = (δ : PG F) • z :=
      by rw [mul_smul, mul_smul, inv_smul_smul, hz]
  have hTmem : ((δ : PG F) * γ * (δ : PG F)⁻¹) • ((δ : PG F) • ω) ∈ T ((δ : PG F) • ω) := by
    have hω' : (δ : PG F) • ω = ((D.j δ * D.rep ω : Gf) : Gf ⧸ D.H) :=
        by have := D.mk_smulO δ (D.rep ω); rwa [rep_spec_jl] at this
    refine ⟨_, QuotientGroup.eq.1 ((rep_spec_jl D _).trans hω'), ?_⟩
    rw [mul_smul, mul_smul, inv_smul_smul, hs, D.mk_smulO, mul_inv_cancel_left, mul_assoc]
  have h10 : ((δ : PG F) * γ * (δ : PG F)⁻¹).out 1 0 ≠ 0 := fun h0 => by
    obtain ⟨v⟩ := (inferInstance : Nonempty I)
    have hfix : Fix ![0, 1] ((δ : PG F) * ((γ.out : GL2 F) : PG F) * (δ : PG F)⁻¹) := by
      rw [QuotientGroup.out_eq']
      exact ⟨((δ : PG F) * γ * (δ : PG F)⁻¹).out 1 1,
             funext fun i => by fin_cases i <;> simp [vecMul, dotProduct, Fin.sum_univ_two, h0]⟩
    obtain ⟨c', hc'⟩ := (fix_conj_jl ![0, 1] γ.out δ).1 hfix
    exact no_eig_of_ell D.σ v γ.out (hell v) (vecMul_ne_jl e01_ne δ) c' hc'
  have hht : D.HtY ![0, 1] ((δ : PG F) • ω, (δ : PG F) • z) ^ 2 ≤ Cm := by
    set γ' := (δ : PG F) * γ * (δ : PG F)⁻¹; set ω' := (δ : PG F) • ω; set z' := (δ : PG F) • z
    have hB := htY_smul_jl D hD ![0, 1] e01_ne γ'.out (ω', z')
    rw [QuotientGroup.out_eq', show γ' • ((ω', z') : D.Y) = (γ' • ω',
                                                             z') from Prod.ext rfl hfixδ] at hB
    have hprod := htY_prod_jl D hD (![0, 1] ᵥ* γ'.out.val) ![0, 1] (by simpa [vecMul, dotProduct,
                                                                              Fin.sum_univ_two] using h10) (ω', z')
    rw [← hB] at hprod
    obtain ⟨h1, hh1, hω1⟩ := hTmem
    have hf1 : D.hf ![0, 1] (D.rep (γ' • ω')) = D.hf ![0, 1] (D.rep ω' * h1 * a) := by
      have hm : (D.rep ω' * h1 * a)⁻¹ * D.rep (γ' • ω') ∈ D.H :=
          QuotientGroup.eq.1 (((rep_spec_jl D (γ' • ω')).trans hω1).symm)
      have := hD.lev ![0, 1] e01_ne (D.rep ω' * h1 * a) _ hm; rwa [mul_inv_cancel_left] at this
    have hf2 : D.hf ![0, 1] (D.rep ω') ≤ Cm * D.hf ![0, 1] (D.rep ω' * h1 * a) := by
      have := hCm ![0, 1] e01_ne (D.rep ω' * h1 * a); rwa [mul_inv_cancel_right, hD.lev ![0,
                                                                                          1] e01_ne _ h1 hh1] at this
    have hpos1 := htY_pos_jl D hD ![0, 1] e01_ne (ω', z'); have hpos2 := htY_pos_jl D hD ![0,
                                                                                           1] e01_ne (γ' • ω', z')
    simp only [show ∀ u, D.HtY ![0, 1] (u, z') = (∏ v, |(z' v).1.im|) * D.hf ![0,
                                                                               1] (D.rep u) from fun _ => by simp [Dat.HtY, Dat.Ht]] at hprod hpos1 hpos2 ⊢
    rw [hf1] at hprod hpos2
    have hP0 : 0 ≤ ∏ v, |(z' v).1.im| := Finset.prod_nonneg fun _ _ => abs_nonneg _
    have k1 : (∏ v, |(z' v).1.im|) * D.hf ![0, 1] (D.rep ω') ≤ Cm * ((∏ v,
                                                                      |(z' v).1.im|) * D.hf ![0,
                                                                                              1] (D.rep ω' * h1 * a)) := by
      nlinarith [mul_le_mul_of_nonneg_left hf2 hP0]
    have hCm0 : 0 ≤ Cm := by by_contra hn; nlinarith [mul_neg_of_neg_of_pos (not_le.1 hn) hpos2]
    nlinarith [mul_le_mul_of_nonneg_right k1 hpos1.le, mul_le_mul_of_nonneg_left hprod hCm0]
  refine ⟨(δ : PG F), (((δ : PG F) • ((γ, ω) : D.Cj × D.Om)), (δ : PG F) • z), ⟨hfixδ, ?_, ?_, hht,
                                                                                hTmem⟩, rfl⟩
  · change Sg C c ((δ : PG F) • z : D.Xs); rw [show (δ : PG F) = (b : PG F) * (g : PG F) from rfl,
                                               mul_smul, D.mk_smulX]; exact hsg
  · change (δ : PG F) • ω ∈ W; rw [hδω]; exact ⟨x', hx', rfl⟩

-- === Fell ===

theorem pf_Fell_jl : C4 → E0a → KernelTermsInvariantBounded → E0d → E1 → E3 → Ecut → Fsum → F2 → F3 → F4 → Fell := by
  intro hC4 hE0a _ _ hE1 hE3 hEcut hFsum hF2 hF3 hF4 F I Gf _ _ _ D hD ι _ a
  have : Nonempty I := by have := hD.two; infer_instance
  obtain ⟨f, hf1, hf2, hR⟩ := orbit_reps (G := PG F) (α := D.Cj × D.Om)
  choose Sa hSa using fun i => hF4 F I Gf D hD (a i)
  let Sset : Set (D.Cj × D.Om) :=
      {p | p ∈ range f ∧ D.TotEll (D.el p.1).out ∧ D.Te a (D.el p.1).out (D.rep p.2) ≠ 0 ∧ Finite (stabilizer (PG F) p)}
  have hSfin : Sset.Finite := (finite_iUnion fun i => (hSa i).1.image f).subset $ by
    rintro p ⟨⟨q, rfl⟩, htot, hte, _⟩
    obtain ⟨i, hi⟩ := kk_supp D a (D.el (f q).1) (f q).2 hte
    obtain ⟨δ, hδ⟩ := (hSa i).2 (D.el (f q).1) (f q).2 htot hi
    exact mem_iUnion.2 ⟨i, δ • f q, hδ, by rw [hf2 (f q) (δ • f q) (mem_orbit _ δ),
                                               hf2 q (f q) (hf1 q)]⟩
  refine ⟨hSfin.toFinset, fun p hp => by rw [Set.Finite.mem_toFinset] at hp; exact ⟨hp.2.1,
                                                                                    hp.2.2.2⟩, fun k hk b hb => ?_⟩
  let u (γ : PG F) (y : D.Y) : ℂ := if IsEll γ then D.kk k a γ y else 0
  have hu_meas γ : Measurable (u γ) := by by_cases h : IsEll γ <;> simp [u, h, meas_kk D k a hk]
  obtain ⟨c₀, hc₀, hmink⟩ := hD.mink; obtain ⟨C, hC⟩ := hE1 F I Gf ι D k a hk c₀ hc₀
  have hbd y : ∑' γ, ‖u γ y‖ₑ ≤ (C : ℝ≥0∞) := by
    obtain ⟨s, hs, hsy⟩ := hmink y.2 (D.rep y.1)
    calc _ ≤ ∑' γ, {γ : PG F | ¬Fix s γ}.indicator (fun γ => ‖D.kk k a γ y‖ₑ) γ :=
            ENNReal.tsum_le_tsum fun γ => by by_cases h : IsEll γ; simp [u, h,
                                                                         indicator_of_mem (show γ ∈ {γ | ¬Fix s γ} from h s hs)]; simp [u, h]
      _ = ∑' γ : {γ : PG F // ¬Fix s γ}, ‖D.kk k a γ.1 y‖ₑ := (_root_.tsum_subtype _ _).symm
      _ ≤ C := hC y s hs hsy
  have hfin : ∫⁻ y, oR (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY < ∞ :=
    ((lintegral_mono fun y => by gcongr; exact hbd y).trans_eq (lintegral_mul_const' _ _ ENNReal.coe_ne_top)).trans_lt
      (ENNReal.mul_lt_top (hE3 F I Gf D hD b hb) ENNReal.coe_lt_top)
  obtain ⟨hb', hFs⟩ := hFsum F I Gf D hD b hb; obtain ⟨hmeas', hint', hintY,
                                                       heq⟩ := hFs u hu_meas hfin
  refine ⟨hintY, heq.trans ?_⟩
  obtain ⟨hcount, hsig, hpres, -⟩ := hE0a F I Gf D hD
  have : Countable (PG F) := hcount; have : Countable D.Cj := hcount; have : Countable D.Om := hD.cO
  have : SigmaFinite (volume : Measure D.Xs) :=
      hsig; have : DiscreteMeasurableSpace (D.Cj × D.Om) := ⟨fun s => s.to_countable.measurableSet⟩
  choose β hβ using fun p : D.Cj × D.Om => (hEcut F I Gf D hD).2 p.2 (stabilizer (PG F) p) fun g hg => congrArg Prod.snd (mem_stabilizer_iff.1 hg)
  have hinv (g : PG F) (y : (D.Cj × D.Om) × D.Xs) : u (D.el (g • y).1.1) ((g • y).1.2,
                                                                          (g • y).2) = u (D.el y.1.1) (y.1.2, y.2) := by
    rcases y with ⟨⟨γ, ω⟩, z⟩; show u (g * D.el γ * g⁻¹) (g • ((ω, z) : D.Y)) = u (D.el γ) (ω, z)
    simp only [u, isEll_conj_jl, kk_conj D k a hk]
  obtain ⟨hintR, hsum⟩ := hC4 (PG F) (D.Cj × D.Om) D.Xs volume hpres (fun p => b (p.1.2, p.2)) hb'
    (fun p => u (D.el p.1.1) (p.1.2, p.2)) hmeas' hinv hint' (range f) hR β fun r _ => hβ r
  let g' (r : D.Cj × D.Om) := ∫ x, β r x • u (D.el r.1) (r.2, x)
  let h' (p : D.Cj × D.Om) :=
      (Nat.card (stabilizer (PG F) p) : ℂ)⁻¹ * (D.Te a (D.el p.1).out (D.rep p.2) * D.orb k (D.el p.1).out)
  have hind : (range f).indicator g' = Sset.indicator h' := funext fun ⟨γ, ω⟩ => by
    by_cases hpR : (γ, ω) ∈ range f
    · rw [indicator_of_mem hpR]
      by_cases hS : (γ, ω) ∈ Sset
      · rw [indicator_of_mem hS]
        have hell : IsEll (D.el γ) := fun s hs ⟨c,
                                                hc⟩ => let ⟨v⟩ := ‹Nonempty I›; no_eig_of_ell D.σ v (D.el γ).out (hS.2.1 v) hs c hc
        simp only [g', u, hell, ite_true]
        exact (hF3 F I Gf ι D k a hk (D.el γ) ω hS.2.1 hS.2.2.1).2 (β (γ, ω)) (hβ (γ, ω))
      · rw [indicator_of_notMem hS]; simp only [g', u]
        by_cases hell : IsEll (D.el γ)
        · simp only [hell, ite_true]
          by_cases htot : D.TotEll (D.el γ).out
          · by_cases hte : D.Te a (D.el γ).out (D.rep ω) = 0
            · simp [Dat.kk, Dat.kt, hte]
            · exact (hS ⟨hpR, htot, hte, (hF3 F I Gf ι D k a hk (D.el γ) ω htot hte).1⟩).elim
          · exact hF2 F I Gf ι D k a hk (D.el γ) ω htot (β (γ, ω)) (hβ (γ, ω)) (by simpa only [u,
                                                                                               hell, ite_true] using hintR (γ, ω) hpR)
        · simp [hell]
    · rw [indicator_of_notMem hpR, indicator_of_notMem fun (h : (γ, ω) ∈ Sset) => hpR h.1]
  have h1 := (hasSum_subtype_iff_indicator (f := g') (s := range f)).1 hsum; rw [hind] at h1
  have h2 : HasSum (Sset.indicator h') (geo D k a hSfin.toFinset) := by
    rw [show geo D k a hSfin.toFinset = ∑ p ∈ hSfin.toFinset, Sset.indicator h' p from
      Finset.sum_congr rfl fun p hp => (indicator_of_mem (by simpa using hp) h').symm]
    exact hasSum_sum_of_ne_finset_zero fun p hp => indicator_of_notMem (by simpa using hp) _
  exact h1.unique h2

-- === F5: Kernel trace bound ===

theorem kernel_trace_bound_proof_jl : E0d → E1 → F5 := by
  intro _ hE1 F I Gf ι _ _ _ _ D k a hH
  obtain ⟨C, hC⟩ := hE1 F I Gf ι D k a hH 1 one_pos
  refine ⟨C, fun T hT y => ⟨fun hy γ s hs _ => hy s hs, fun hy => ?_⟩⟩
  simp only [Dat.abelian₂, mem_ofPred_eq, not_forall, not_le] at hy; obtain ⟨s, hs, hsT⟩ := hy
  calc ∑' γ : PG F, ‖(D.LamF T γ).indicator (D.kk k a γ) y‖ₑ
      ≤ ∑' γ, {γ : PG F | ¬Fix s γ}.indicator (fun γ => ‖D.kk k a γ y‖ₑ) γ :=
          ENNReal.tsum_le_tsum fun γ => by
          by_cases hγ : y ∈ D.LamF T γ
          · rw [indicator_of_mem hγ,
                indicator_of_mem (show γ ∈ {γ | ¬Fix s γ} from fun hf => absurd (hγ s hs hf) (not_le.2 hsT))]
          · rw [indicator_of_notMem hγ]; simp
    _ = ∑' γ : {γ : PG F // ¬Fix s γ}, ‖D.kk k a γ.1 y‖ₑ := (_root_.tsum_subtype _ _).symm
    _ ≤ C := hC y s hs (hT.trans hsT).le

-- === ConstantTermVanishingAlt ===

theorem unipotent_integrand_vanishes_proof_jl : B1a → UpperHalfPlaneMeasureCoordinates → ConstantTermVanishingAlt := by
  intro hB1 _ I _ _ φ hφ β hβ hβ0 hβinv A B hA hAB u hu hint
  have : SigmaFinite (volume : Measure P) := hB1.1
  let Y1 := {y : ℝ // y ≠ 0}
  let nu1 : Measure Y1 := (Measure.comap Subtype.val volume).withDensity fun y => oR (1 / |y.1|)
  have hY : MeasurableSet {y : ℝ | y ≠ 0} := (measurableSet_singleton 0).compl
  have hemb : MeasurableEmbedding (Subtype.val : Y1 → ℝ) :=
      MeasurableEmbedding.subtype_coe (s := {y : ℝ | y ≠ 0}) hY
  have hmap_wd {α β : Type} [MeasurableSpace α] [MeasurableSpace β] {f : α → β} (hf : MeasurableEmbedding f) (μ : Measure α) (g : β → ℝ≥0∞) :
      Measure.map f (μ.withDensity fun x => g (f x)) = (Measure.map f μ).withDensity g :=
          Measure.ext fun s hs => by
    rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
        withDensity_apply _ hs, hf.restrict_map, hf.lintegral_map]
  have hmap_nu1 : Measure.map Subtype.val nu1 = (volume : Measure ℝ).withDensity fun y => oR (1 / |y|) := by
    have h0 : Measure.map (Subtype.val : Y1 → ℝ) (Measure.comap Subtype.val volume) = volume := by
      rw [show Measure.map (Subtype.val : Y1 → ℝ) (Measure.comap Subtype.val volume) = volume.restrict (range (Subtype.val : Y1 → ℝ)) from hemb.map_comap volume,
        show range (Subtype.val : Y1 → ℝ) = {0}ᶜ from Set.ext fun _ => by simp]
      exact Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.2 (measure_singleton 0))
    exact (hmap_wd hemb (Measure.comap Subtype.val volume) fun y => oR (1 / |y|)).trans (by rw [h0])
  have : SigmaFinite nu1 :=
      SigmaFinite.of_map nu1 hemb.measurable.aemeasurable (by rw [hmap_nu1]; infer_instance)
  let scl (t : ℝ) (ht : t ≠ 0) (y : Y1) : Y1 := ⟨t * y.1, mul_ne_zero ht y.2⟩
  have hmpscl (t : ℝ) (ht : t ≠ 0) : MeasurePreserving (scl t ht) nu1 nu1 := by
    have hm : Measurable (scl t ht) :=
        ((measurable_const_mul t).comp measurable_subtype_coe).subtype_mk
    refine ⟨hm, ?_⟩
    have hmr : Measure.map (t * ·) ((volume : Measure ℝ).withDensity fun y => oR (1 / |y|)) = (volume : Measure ℝ).withDensity fun y => oR (1 / |y|) := by
      have hembm : MeasurableEmbedding (t * ·) := (Homeomorph.mulLeft₀ t ht).measurableEmbedding
      have hpt : (volume : Measure ℝ).withDensity (fun y => oR (1 / |y|)) = oR |t| • (volume : Measure ℝ).withDensity fun y => oR (1 / |t * y|) := by
        rw [← withDensity_smul _ (by fun_prop)]; congr 1; funext y; simp only [Pi.smul_apply,
                                                                               smul_eq_mul]
        rw [← ENNReal.ofReal_mul (abs_nonneg t), abs_mul]; congr 1
        rw [one_div, one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.2 ht), one_mul]
      have hc : oR |t| * oR |t⁻¹| = 1 := by rw [← ENNReal.ofReal_mul (abs_nonneg t), ← abs_mul,
                                                mul_inv_cancel₀ ht, abs_one, ENNReal.ofReal_one]
      conv_lhs => rw [hpt]
      rw [Measure.map_smul, hmap_wd hembm volume (fun y : ℝ => oR (1 / |y|)),
          Real.map_volume_mul_left ht, withDensity_smul_measure, smul_smul, hc, one_smul]
      exact hembm.measurable.aemeasurable
    have hv : Measure.map Subtype.val (Measure.map (scl t ht) nu1) = Measure.map Subtype.val nu1 := by
      rw [Measure.map_map hemb.measurable hm,
          show Subtype.val ∘ scl t ht = (t * ·) ∘ Subtype.val from rfl,
        ← Measure.map_map (measurable_const_mul t) hemb.measurable, hmap_nu1, hmr]
    rw [← hemb.comap_map (Measure.map (scl t ht) nu1), hv, hemb.comap_map]
  let Φ : (I → ℝ) × (I → Y1) ≃ᵐ X I :=
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ Y1 I).symm.trans (MeasurableEquiv.piCongrRight fun _ : I => ptE_jl)
  have hΦ : MeasurePreserving Φ ((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1)) volume :=
    (measurePreserving_pi _ _ fun _ => pt_mp).comp (MeasurePreserving.symm _ (measurePreserving_arrowProdEquivProdArrow ℝ Y1 I (fun _ => volume) (fun _ => nu1)))
  let b (y : I → Y1) : ℝ := β (Φ (0, y))
  have hb : Measurable b := hβ.comp (Φ.measurable.comp (measurable_const.prodMk measurable_id))
  have hβΦ x y : β (Φ (x,
                       y)) = b y := (hβinv x 0 (fun v => (y v).1) (fun v => (y v).2) 1 one_pos).trans $
    congrArg β (funext fun v => Subtype.ext (by change ((1 * (y v).1 : ℝ) : ℂ) * ((0 : ℝ) + Complex.I) = ((y v).1 : ℂ) * ((0 : ℝ) + Complex.I); simp))
  have huΦ x y : u (Φ (x,
                       y)) = if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v, |(y v).1| ≤ B then ∏ v, φ v (x v) else 0 := hu x (fun v => (y v).1) (fun v => (y v).2)
  have hint' : Integrable (fun p : (I → ℝ) × (I → Y1) => b p.2 • (if A / ∏ v, (1 + p.1 v ^ 2) ≤ ∏ v,
                                                                  |(p.2 v).1| ∧ ∏ v, |(p.2 v).1| ≤ B then ∏ v, φ v (p.1 v) else 0))
      ((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1)) :=
    ((hΦ.integrable_comp_emb Φ.measurableEmbedding).2 hint).congr (ae_of_all _ fun ⟨x,
                                                                                    y⟩ => by change β (Φ (x, y)) • u (Φ (x, y)) = _; rw [hβΦ, huΦ])
  let Lg (y : I → Y1) : ℝ := ∑ v, Real.log |(y v).1|
  have hLgm : Measurable Lg :=
      Finset.measurable_sum _ fun v _ => Real.measurable_log.comp (continuous_abs.measurable.comp (measurable_subtype_coe.comp (measurable_pi_apply v)))
  have hcond (x : I → ℝ) (y : I → Y1) : (A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v,
                                         |(y v).1| ≤ B) ↔ Lg y ∈ Icc (Real.log A - ∑ v,
                                                                      Real.log (1 + x v ^ 2)) (Real.log B) := by
    have hp : 0 < ∏ v, |(y v).1| := Finset.prod_pos fun v _ => abs_pos.2 (y v).2
    have hq : 0 < ∏ v, (1 + x v ^ 2) := Finset.prod_pos fun _ _ => by positivity
    rw [Set.mem_Icc, show Lg y = Real.log (∏ v,
                                           |(y v).1|) from (Real.log_prod fun v _ => abs_ne_zero.2 (y v).2).symm,
      show Real.log A - ∑ v, Real.log (1 + x v ^ 2) = Real.log (A / ∏ v,
                                                                (1 + x v ^ 2)) by rw [Real.log_div hA.ne' hq.ne', Real.log_prod fun _ _ => by positivity],
      Real.log_le_log_iff (div_pos hA hq) hp, Real.log_le_log_iff hp (hA.trans hAB)]
  let m : Measure ℝ := Measure.map Lg ((Measure.pi fun _ : I => nu1).withDensity fun y => oR (b y))
  have hminv (c : ℝ) (S : Set ℝ) (hS : MeasurableSet S) : m ((c + ·) ⁻¹' S) = m S := by
    have hcard : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    set t := Real.exp (c / Fintype.card I); have ht : 0 < t := Real.exp_pos _
    have hlog : (Fintype.card I : ℝ) * Real.log t = c := by rw [Real.log_exp]; field_simp
    have hS' : MeasurableSet (Lg ⁻¹' S) := hLgm hS
    have hpre : Lg ⁻¹' ((c + ·) ⁻¹' S) = (fun y : I → Y1 => fun v => scl t ht.ne' (y v)) ⁻¹' (Lg ⁻¹' S) :=
        Set.ext fun y => by
      simp only [Set.mem_preimage]
      rw [show Lg (fun v => scl t ht.ne' (y v)) = c + Lg y by
        rw [← hlog]; simp only [Lg, scl, abs_mul, abs_of_pos ht]
        rw [Finset.sum_congr rfl fun v _ => Real.log_mul ht.ne' (abs_ne_zero.2 (y v).2),
            Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    have hscl : MeasurePreserving (fun y : I → Y1 => fun v => scl t ht.ne' (y v)) (Measure.pi fun _ => nu1) (Measure.pi fun _ => nu1) :=
      measurePreserving_pi _ _ fun _ => hmpscl t ht.ne'
    have hpm : MeasurableSet ((fun y : I → Y1 => fun v => scl t ht.ne' (y v)) ⁻¹' (Lg ⁻¹' S)) :=
        hscl.measurable hS'
    rw [Measure.map_apply hLgm ((measurable_const_add c) hS), Measure.map_apply hLgm hS, hpre,
      withDensity_apply _ hpm, withDensity_apply _ hS', ← lintegral_indicator hpm, ← lintegral_indicator hS',
      ← hscl.lintegral_comp ((show Measurable (fun a => oR (b a)) from ENNReal.measurable_ofReal.comp hb).indicator hS')]
    refine lintegral_congr fun y => ?_
    by_cases hy : (fun v => scl t ht.ne' (y v)) ∈ Lg ⁻¹' S
    · rw [indicator_of_mem (show y ∈ _ ⁻¹' _ from hy), indicator_of_mem hy]
      exact congrArg oR (hβinv 0 0 (fun v => (y v).1) (fun v => (y v).2) t ht)
    · rw [indicator_of_notMem (show y ∉ _ ⁻¹' _ from hy), indicator_of_notMem hy]
  have hlt (x : I → ℝ) : Real.log A - ∑ v, Real.log (1 + x v ^ 2) < Real.log B := by
    have : 0 ≤ ∑ v, Real.log (1 + x v ^ 2) :=
        Finset.sum_nonneg fun v _ => Real.log_nonneg (by linarith [sq_nonneg (x v)])
    linarith [Real.log_lt_log hA hAB]
  have : (ae (volume : Measure (I → ℝ))).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨x0, hx0⟩ := hint'.prod_right_ae.exists
  let J0 := Icc (Real.log A - ∑ v, Real.log (1 + x0 v ^ 2)) (Real.log B)
  have hfin : m J0 ≠ ∞ := by
    have hP0 : (∏ v, φ v (x0 v)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => (hφ v).2.2.2.2 (x0 v)
    have hTint : Integrable ((Lg ⁻¹' J0).indicator b) (Measure.pi fun _ : I => nu1) :=
      (hx0.norm.div_const ‖∏ v, φ v (x0 v)‖).congr (ae_of_all _ fun y => by
        dsimp only; by_cases h : Lg y ∈ J0
        · rw [ite_eq_left ((hcond x0 y).2 h), indicator_of_mem (show y ∈ Lg ⁻¹' J0 from h),
              norm_smul, Real.norm_of_nonneg (hβ0 _), mul_div_assoc, div_self (norm_ne_zero_iff.2 hP0), mul_one]
        · rw [ite_eq_right (mt (hcond x0 y).1 h), indicator_of_notMem (show y ∉ Lg ⁻¹' J0 from h),
              smul_zero, norm_zero, zero_div])
    rw [Measure.map_apply hLgm measurableSet_Icc, withDensity_apply _ (hLgm measurableSet_Icc),
        ← lintegral_indicator (hLgm measurableSet_Icc)]
    exact ((lintegral_congr fun y => by simp only [indicator]; split_ifs <;> simp).trans_lt hTint.lintegral_lt_top).ne
  -- Haar uniqueness on ℝ
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ a c : ℝ, a ≤ c → (m (Icc a c)).toReal = R * (c - a) := by
    have hI : m.IsAddLeftInvariant :=
        ⟨fun c => Measure.ext fun S hS => by rw [Measure.map_apply (measurable_const_add c) hS]; exact hminv c S hS⟩
    set a0 := Real.log A - ∑ v, Real.log (1 + x0 v ^ 2); set ℓ := Real.log B - a0
    have hℓ : 0 < ℓ := by linarith [hlt x0]
    have hL : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Icc (x - ℓ / 2) (x - ℓ / 2 + ℓ),
                                                     Icc_mem_nhds (by linarith) (by linarith), by
      have h := hminv (a0 - (x - ℓ / 2)) J0 measurableSet_Icc
      rw [preimage_const_add_Icc, show a0 - (a0 - (x - ℓ / 2)) = x - ℓ / 2 by ring,
          show Real.log B - (a0 - (x - ℓ / 2)) = x - ℓ / 2 + ℓ by ring] at h
      exact h ▸ hfin.lt_top⟩⟩
    refine ⟨(Measure.addHaarScalarFactor m volume : ℝ), fun a c hac => ?_⟩
    have := congrArg (fun μ : Measure ℝ => μ (Icc a c)) (Measure.isAddLeftInvariant_eq_smul m (volume : Measure ℝ))
    rw [this, Measure.smul_apply, Real.volume_Icc, ENNReal.smul_def, smul_eq_mul,
        ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal (sub_nonneg.2 hac)]
  -- Integrate out y then x
  have heq : ∫ z, β z • u z = ∫ p : (I → ℝ) × (I → Y1),
      b p.2 • (if A / ∏ v, (1 + p.1 v ^ 2) ≤ ∏ v, |(p.2 v).1| ∧ ∏ v, |(p.2 v).1| ≤ B then ∏ v,
               φ v (p.1 v) else 0)
      ∂((volume : Measure (I → ℝ)).prod (Measure.pi fun _ : I => nu1)) :=
    (hΦ.integral_comp' (fun z => β z • u z)).symm.trans (integral_congr_ae (ae_of_all _ fun ⟨x,
                                                                                             y⟩ => by
      change β (Φ (x, y)) • u (Φ (x, y)) = _; rw [hβΦ, huΦ]))
  rw [heq, integral_prod _ hint']
  have hinner (x : I → ℝ) : ∫ y, b y • (if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v,
                                        |(y v).1| ≤ B then ∏ v, φ v (x v) else 0) ∂(Measure.pi fun _ : I => nu1) =
      (∏ v, φ v (x v)) * ((R * ((Real.log B - Real.log A) + ∑ v,
                                Real.log (1 + x v ^ 2)) : ℝ) : ℂ) := by
    let J := Icc (Real.log A - ∑ v, Real.log (1 + x v ^ 2)) (Real.log B)
    have hS : MeasurableSet (Lg ⁻¹' J) := hLgm measurableSet_Icc
    have e1 : (fun y : I → Y1 => b y • (if A / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |(y v).1| ∧ ∏ v,
                                        |(y v).1| ≤ B then ∏ v, φ v (x v) else 0)) =
        fun y => (((Lg ⁻¹' J).indicator b y : ℝ) : ℂ) * ∏ v, φ v (x v) := funext fun y => by
      by_cases h : Lg y ∈ J
      · rw [ite_eq_left ((hcond x y).2 h), indicator_of_mem (show y ∈ Lg ⁻¹' J from h), real_smul]
      · rw [ite_eq_right (mt (hcond x y).1 h), indicator_of_notMem (show y ∉ Lg ⁻¹' J from h),
            smul_zero]; simp
    rw [e1, integral_mul_const, integral_complex_ofReal, integral_indicator hS, mul_comm,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => hβ0 _) hb.aestronglyMeasurable,
      ← withDensity_apply _ hS, ← Measure.map_apply hLgm measurableSet_Icc, hR _ _ (hlt x).le,
      show Real.log B - (Real.log A - ∑ v,
                         Real.log (1 + x v ^ 2)) = (Real.log B - Real.log A) + ∑ v, Real.log (1 + x v ^ 2) by ring]
  rw [integral_congr_ae (ae_of_all _ hinner)]
  -- integral_prod_log
  let ψ (w v : I) (t : ℝ) : ℂ := (if v = w then (Real.log (1 + t ^ 2) : ℂ) else 1) * φ v t
  have hP : Integrable (fun x : I → ℝ => ∏ v,
                        φ v (x v)) := by rw [volume_pi]; exact Integrable.fintype_prod fun v => (hφ v).2.1
  have hψP w : Integrable (fun x : I → ℝ => ∏ v, ψ w v (x v)) := by
    rw [volume_pi]; exact Integrable.fintype_prod fun v => by by_cases hv : v = w <;> simp [ψ, hv,
                                                                                            (hφ _).2.1, (hφ _).2.2.1]
  have hkey (x : I → ℝ) : (∏ v, φ v (x v)) * ((R * ((Real.log B - Real.log A) + ∑ v,
                                                    Real.log (1 + x v ^ 2)) : ℝ) : ℂ) =
      (R * (Real.log B - Real.log A) : ℂ) * ∏ v, φ v (x v) + ∑ w, (R : ℂ) * ∏ v, ψ w v (x v) := by
    have hψw w : ∏ v, ψ w v (x v) = (Real.log (1 + x w ^ 2) : ℂ) * ∏ v, φ v (x v) := by
      simp only [ψ, Finset.prod_mul_distrib]
      rw [Finset.prod_eq_single w (fun _ _ hv => by simp [hv]) (by simp)]; simp
    simp_rw [hψw]; rw [← Finset.mul_sum, ← Finset.sum_mul]; push_cast; ring
  simp_rw [hkey]
  obtain ⟨v0, _, _⟩ := exists_pair_ne I
  have hz0 w : ∏ v, ∫ t, ψ w v t = 0 := by
    obtain ⟨v, hv⟩ := exists_ne w
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by simpa [ψ, hv] using (hφ v).2.2.2.1)
  rw [integral_add (hP.const_mul _) (integrable_finsetSum _ fun w _ => (hψP w).const_mul _)]
  rw [integral_const_mul, integral_fintype_prod_volume_eq_prod,
    Finset.prod_eq_zero (Finset.mem_univ v0) (hφ v0).2.2.2.1, mul_zero, zero_add]
  rw [integral_finsetSum _ fun w _ => (hψP w).const_mul _]
  exact Finset.sum_eq_zero fun w _ => by
    rw [integral_const_mul, integral_fintype_prod_volume_eq_prod, hz0, mul_zero]

-- === DiagonalTruncatedIntegralZero ===

theorem diagonal_truncated_integral_zero_jl : B1a → UpperHalfPlaneMeasureCoordinates → DiagonalIntegrandVanishes → C1 → E0a → KernelTermsInvariantBounded → E0d → Ecut → Fcen → ConstantTermVanishingAlt → DiagonalTruncatedIntegralZero := by
  intro _ _ _ _ hE0a _ _ hEcut _ hF6c F I Gf ι _ _ _ _ D k a hH T hT γ ω h01 h10 β hβ hint
  obtain ⟨hcount, _, hpres, _, _, _, hbor, _⟩ := hE0a F I Gf D hH.ax
  have := hH.ax.two; have : Countable (PG F) := hcount; have : BorelSpace D.Xs := hbor
  set g := (γ : PG F).out
  have hgq : (g : PG F) = (γ : PG F) := QuotientGroup.out_eq' _
  have ⟨g01, g10⟩ : g 0 1 = 0 ∧ g 1 0 = 0 := by
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL2 F)) γ; obtain ⟨z1, z2,
                                                                              _⟩ := center_entries z.2
    rw [show g = γ * z.1 from hz]; simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h10, z1, z2]
  have hkk (z : D.Xs) : D.kk k a (γ : PG F) (ω,
                                             z) = D.Te a g (D.rep ω) * ∏ v, (q1 (k v) (z v) (D.r v g • z v) * j1 (k v) (D.r v g) (z v)) := by
    change D.Te a g (D.rep ω) * (qq k z (D.act g z) * D.J k g z) = _
    simp only [qq, Dat.J, Dat.act, Finset.prod_mul_distrib]
  by_cases hc : D.Te a g (D.rep ω) = 0
  · have h0 z : (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω,
                                                                       z) = 0 := by rw [indicator_apply]; split_ifs <;> simp [hkk, hc]
    simp [h0]
  obtain ⟨i, hi⟩ := kk_supp D a (γ : PG F) ω hc; obtain ⟨htr0,
                                                         htr1⟩ := kk_reg D k a hH (γ : PG F) ω i hi
  have hne : g 0 0 ≠ g 1 1 := fun h => htr1 (by rw [trace_fin_two, det_fin_two, g01, g10, h]; ring)
  choose φ hφc hφe hφi hφl hφ0 hφn using fun v => diagonal_integrand_vanishes_proof_jl (k v) (hH.four v) (D.r v g)
    (show D.σ v (g 0 1) = 0 by rw [g01, map_zero]) (show D.σ v (g 1 0) = 0 by rw [g10,
                                                                                  map_zero]) fun h => hne ((D.σ v).injective h)
  by_cases hz : ∃ v, φ v = 0
  · obtain ⟨v, hv⟩ := hz
    have h0 (z : D.Xs) : D.kk k a (γ : PG F) (ω, z) = 0 := by
      rw [hkk, Finset.prod_eq_zero (Finset.mem_univ v), mul_zero]
      have := hφe v ((z v).1.re / (z v).1.im) (z v).1.im (z v).2
      rw [show pt ((z v).1.re / (z v).1.im) (z v).1.im (z v).2 = z v from ptE_jl.right_inv (z v),
          hv] at this; exact this
    have h0' z : (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω,
                                                                        z) = 0 := by rw [indicator_apply]; split_ifs <;> simp [h0]
    simp [h0']
  push Not at hz; have hφn' v x : φ v x ≠ 0 := (hφn v).resolve_left (hz v) x
  have h1pos : 0 < D.hf ![0, 1] (D.rep ω) := hH.ax.pos _ (by simp) _
  have h2pos : 0 < D.hf ![1, 0] (D.rep ω) := hH.ax.pos _ (by simp) _
  have h12 : D.hf ![0, 1] (D.rep ω) * D.hf ![1, 0] (D.rep ω) ≤ 1 := by simpa using hH.ax.prod ![0,
                                                                                                1] ![1, 0] (by simp) (D.rep ω)
  have hH01 (z : D.Xs) : D.HtY ![0, 1] (ω, z) = (∏ v, |(z v).1.im|) * D.hf ![0,
                                                                             1] (D.rep ω) := by simp [Dat.HtY, Dat.Ht]
  have hH10 (z : D.Xs) : D.HtY ![1, 0] (ω, z) = (∏ v, |(z v).1.im| / ‖(z v).1‖ ^ 2) * D.hf ![1,
                                                                                             0] (D.rep ω) := by simp [Dat.HtY, Dat.Ht]
  have hLam (z : D.Xs) : (ω, z) ∈ D.LamF T (γ : PG F) ↔ D.HtY ![0, 1] (ω, z) ≤ T ∧ D.HtY ![1, 0] (ω,
                                                                                                  z) ≤ T := by
    simp only [Dat.LamF, mem_ofPred_eq, Fix]
    refine ⟨fun h => ⟨h _ (by simp) ⟨g 1 1, funext fun j => by fin_cases j <;> simp [vecMul,
                                                                                     dotProduct, Fin.sum_univ_two, show (γ : PG F).out = g from rfl, g10]⟩,
      h _ (by simp) ⟨g 0 0, funext fun j => by fin_cases j <;> simp [vecMul, dotProduct,
                                                                     Fin.sum_univ_two, show (γ : PG F).out = g from rfl, g01]⟩⟩,
      fun ⟨h1, h2⟩ s hs ⟨c, hc⟩ => ?_⟩
    change s ᵥ* g.val = c • s at hc
    have e0 : s 0 * g 0 0 = c * s 0 := by simpa [vecMul, dotProduct, Fin.sum_univ_two, g01,
                                                 g10] using congrFun hc 0
    have e1 : s 1 * g 1 1 = c * s 1 := by simpa [vecMul, dotProduct, Fin.sum_univ_two, g01,
                                                 g10] using congrFun hc 1
    by_cases hs0 : s 0 = 0
    · have hs1 : s 1 ≠ 0 := fun h => hs (funext fun j => by fin_cases j <;> simp [hs0, h])
      rw [show s = s 1 • ![0, 1] from funext fun j => by fin_cases j <;> simp [hs0],
          htY_smulc_jl D hH.ax _ (by simp) _ hs1]; exact h1
    · have hs1 : s 1 = 0 := by
        by_contra h
        exact hne ((mul_left_cancel₀ hs0 (show s 0 * g 0 0 = s 0 * c by linear_combination e0)).trans
          (mul_left_cancel₀ h (show s 1 * g 1 1 = s 1 * c by linear_combination e1)).symm)
      rw [show s = s 0 • ![1, 0] from funext fun j => by fin_cases j <;> simp [hs1],
          htY_smulc_jl D hH.ax _ (by simp) _ hs0]; exact h2
  set S := stabilizer (PG F) (((γ : PG F), ω) : D.Cj × D.Om)
  have hstab (δ : PG F) (hδ : δ ∈ S) : δ * (γ : PG F) * δ⁻¹ = γ ∧ δ • ω = ω := by
    rw [mem_stabilizer_iff] at hδ; exact ⟨(D.smulC δ (γ : PG F)).symm.trans (congrArg Prod.fst hδ),
                                          congrArg Prod.snd hδ⟩
  have hdiag (δ : PG F) (hδ : δ ∈ S) : δ.out 0 1 = 0 ∧ δ.out 1 0 = 0 ∧ ∏ v, |D.σ v (δ.out 0 0) / D.σ v (δ.out 1 1)| = 1 := by
    obtain ⟨h3, h2⟩ := hstab δ hδ
    have hcomm := pf_Fcen_jl F g δ.out htr0 (by rw [QuotientGroup.out_eq', hgq]; exact h3)
    have a01 :=
        congrArg (fun m : GL2 F => m 0 1) hcomm; have a10 := congrArg (fun m : GL2 F => m 1 0) hcomm
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, g01, g10, mul_zero, zero_mul,
               add_zero, zero_add] at a01 a10
    have d01 : δ.out 0 1 = 0 :=
        by by_contra h; exact hne (mul_left_cancel₀ h (by linear_combination -a01))
    have d10 : δ.out 1 0 = 0 :=
        by by_contra h; exact hne (mul_left_cancel₀ h (by linear_combination a10))
    refine ⟨d01, d10, ?_⟩
    have hd11 : δ.out 1 1 ≠ 0 := fun h => δ.out.det_ne_zero (by rw [det_fin_two, h, d01]; ring)
    have hr v (w : P) : (D.r v δ.out • w).1.im = D.σ v (δ.out 0 0) / D.σ v (δ.out 1 1) * w.1.im := by
      rw [diag_smul_jl (show D.σ v (δ.out 0 1) = 0 by rw [d01,
                                                          map_zero]) (show D.σ v (δ.out 1 0) = 0 by rw [d10, map_zero]), im_ofReal_mul]; rfl
    have key := htY_smul_jl D hH.ax ![0, 1] e01_ne δ.out ((ω, fun _ => iP) : D.Y)
    rw [show ![0, 1] ᵥ* δ.out.val = δ.out 1 1 • ![0,
                                                  1] from funext fun j => by fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_two, d10],
      htY_smulc_jl D hH.ax _ e01_ne _ hd11, QuotientGroup.out_eq',
      show δ • ((ω, fun _ => iP) : D.Y) = (ω,
                                           D.act δ.out fun _ => iP) from Prod.ext h2 (smulX_out_jl D δ _)] at key
    have key2 := (hH01 (D.act δ.out fun _ => iP)).symm.trans (key.trans (hH01 (fun _ => iP)))
    simp only [Dat.act, hr] at key2; simpa [iP, h1pos.ne'] using key2
  obtain ⟨β0, hβ0⟩ := (hEcut F I Gf D hH.ax).2 ω S fun δ hδ => mem_stabilizer_iff.2 (hstab δ hδ).2
  let N (z : D.Xs) : ℝ := (∏ v, |(z v).1.im|) ^ ((Fintype.card I : ℝ)⁻¹)
  have hNpos z : 0 < N z := rpow_pos_of_pos (Finset.prod_pos fun v _ => abs_pos.2 (z v).2) _
  let p (z : D.Xs) : D.Xs := fun v => pt 0 ((z v).1.im / N z) (div_ne_zero (z v).2 (hNpos z).ne')
  have hpc : Continuous p := continuous_pi fun v => by
    have hNc : Continuous (N : (I → P) → ℝ) :=
      (continuous_finsetProd Finset.univ fun (w : I) _ => (continuous_im.comp (continuous_subtype_val.comp (continuous_apply w))).abs).rpow_const
        fun (z : I → P) => Or.inl (Finset.prod_pos fun w _ => abs_pos.2 (z w).2).ne'
    exact continuous_induced_rng.2 $
      (continuous_ofReal.comp ((continuous_im.comp (continuous_subtype_val.comp (continuous_apply v))).div hNc fun (z : I → P) => (hNpos z).ne')).mul continuous_const
  have hpeq (δ : S) (z : D.Xs) : p (δ.1 • z) = δ.1 • p z := by
    obtain ⟨d01, d10, dprod⟩ := hdiag δ.1 δ.2
    have h01' v : (D.r v δ.1.out) 0 1 = 0 := by change D.σ v (δ.1.out 0 1) = 0; rw [d01, map_zero]
    have h10' v : (D.r v δ.1.out) 1 0 = 0 := by change D.σ v (δ.1.out 1 0) = 0; rw [d10, map_zero]
    have hr v (w : P) : (D.r v δ.1.out • w).1.im = D.σ v (δ.1.out 0 0) / D.σ v (δ.1.out 1 1) * w.1.im :=
        by rw [diag_smul_jl (h01' v) (h10' v), im_ofReal_mul]; rfl
    have hN : N (D.act δ.1.out z) = N z := by simp only [N, Dat.act, hr, abs_mul,
                                                         Finset.prod_mul_distrib, dprod, one_mul]
    rw [smulX_out_jl, smulX_out_jl]; funext v; apply Subtype.ext
    change (((D.r v δ.1.out • z v).1.im / N (D.act δ.1.out z) : ℝ) : ℂ) * ((0 : ℝ) + Complex.I) = (D.r v δ.1.out • p z v).1
    rw [hr, hN, diag_smul_jl (h01' v) (h10' v)]
    change _ = ((D.σ v (δ.1.out 0 0) / D.σ v (δ.1.out 1 1) : ℝ) : ℂ) * ((((z v).1.im / N z : ℝ) : ℂ) * ((0 : ℝ) + Complex.I)); push_cast; ring
  have hβ' : IsCut S (fun z : D.Xs => β0 (p z)) := ⟨hβ0.meas.comp hpc.measurable,
                                                    fun _ => hβ0.nonneg _, fun z => by
    have : (fun δ : S => β0 (p (δ • z))) = fun δ => β0 (δ • p z) :=
        funext fun δ => congrArg β0 (hpeq δ z)
    show HasSum _ 1; rw [this]; exact hβ0.sum (p z)⟩
  let u (z : D.Xs) : ℂ := (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω, z)
  have huinv (δ : S) (z : D.Xs) : u (δ • z) = u z := by
    obtain ⟨h3, h2⟩ := hstab δ.1 δ.2
    have hy : ((ω, (δ.1 • z : D.Xs)) : D.Y) = δ.1 • ((ω, z) : D.Y) := Prod.ext h2.symm rfl
    have hk := kk_conj D k a hH δ.1 (γ : PG F) (ω, z); rw [h3] at hk
    have hm : δ.1 • ((ω, z) : D.Y) ∈ D.LamF T (γ : PG F) ↔ ((ω, z) : D.Y) ∈ D.LamF T (γ : PG F) :=
      ⟨fun h => by have := lamF_smul_jl D hH.ax T _ δ.1⁻¹ _ h; rwa [inv_smul_smul,
                                                                    show δ.1⁻¹ * (γ : PG F) * δ.1⁻¹⁻¹ = γ from (congrArg (fun x => δ.1⁻¹ * x * δ.1⁻¹⁻¹) h3.symm).trans (by group)] at this,
       fun h => by have := lamF_smul_jl D hH.ax T _ δ.1 _ h; rwa [h3] at this⟩
    change (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω,
                                                                  δ.1 • z) = (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω, z); rw [hy]
    by_cases h : ((ω, z) : D.Y) ∈ D.LamF T (γ : PG F)
    · rw [indicator_of_mem (hm.2 h), indicator_of_mem h, hk]
    · rw [indicator_of_notMem (mt hm.1 h), indicator_of_notMem h]
  have hC :=
      (action_integral_swap_proof_jl S D.Xs volume (fun δ => hpres δ.1) β (fun z => β0 (p z)) hβ hβ').2 u
    (((meas_kk D k a hH _).indicator (meas_lamF_jl D hH.ax T _)).comp measurable_prodMk_left) huinv hint
  rw [hC.2]
  have hF := hF6c I φ (fun v => ⟨hφc v, hφi v, hφl v, hφ0 v,
                                 hφn' v⟩) (fun z => β0 (p z)) (hβ0.meas.comp hpc.measurable) (fun _ => hβ0.nonneg _)
    (fun x x' y hy t ht => congrArg β0 $ funext fun v => Subtype.ext $ by
      have hsc : (∏ w, |t * y w|) ^ ((Fintype.card I : ℝ)⁻¹) = t * (∏ w,
                                                                    |y w|) ^ ((Fintype.card I : ℝ)⁻¹) := by
        simp only [abs_mul, Finset.prod_mul_distrib, Finset.prod_const, abs_of_pos ht,
                   Finset.card_univ]
        rw [mul_rpow (by positivity) (Finset.prod_nonneg fun _ _ => abs_nonneg _),
            pow_rpow_inv_natCast ht.le Fintype.card_ne_zero]
      simp only [p, N, pt, mul_im, ofReal_re, ofReal_im, add_im, I_im, zero_add, mul_one, add_zero,
                 zero_mul]
      rw [hsc, mul_div_mul_left _ _ ht.ne'])
    (D.hf ![1, 0] (D.rep ω) / T) (T / D.hf ![0, 1] (D.rep ω)) (div_pos h2pos (by linarith))
    ((div_lt_div_iff₀ (by linarith) h1pos).2 (by nlinarith)) (fun z => (D.Te a g (D.rep ω))⁻¹ * u z)
    (fun x y hy => by
      have hPy : 0 < ∏ v, |y v| := Finset.prod_pos fun v _ => abs_pos.2 (hy v)
      have hQ : 0 < ∏ v, (1 + x v ^ 2) := Finset.prod_pos fun _ _ => by positivity
      have hcond : ((ω, fun v => pt (x v) (y v) (hy v)) : D.Y) ∈ D.LamF T (γ : PG F) ↔
          (D.hf ![1, 0] (D.rep ω) / T / ∏ v, (1 + x v ^ 2) ≤ ∏ v, |y v| ∧ ∏ v, |y v| ≤ T / D.hf ![0,
                                                                                                  1] (D.rep ω)) := by
        refine (hLam _).trans ?_; rw [hH01 (fun v => pt (x v) (y v) (hy v)),
                                      hH10 (fun v => pt (x v) (y v) (hy v))]
        simp only [show ∀ v, |(pt (x v) (y v) (hy v)).1.im| = |y v| from fun _ => by simp [pt],
          show ∀ v, |y v| / ‖(pt (x v) (y v) (hy v)).1‖ ^ 2 = (|y v| * (1 + x v ^ 2))⁻¹ from fun v => by
            rw [Complex.sq_norm, normSq_apply]; simp [pt]
            have h1 : y v * x v * (y v * x v) + y v * y v = |y v| ^ 2 * (1 + x v ^ 2) :=
                by rw [sq_abs]; ring
            have : |y v| ≠ 0 :=
                abs_ne_zero.2 (hy v); have : (1 + x v ^ 2) ≠ 0 := (by positivity); rw [h1]; field_simp,
          Finset.prod_inv_distrib, Finset.prod_mul_distrib, inv_mul_le_iff₀ (mul_pos hPy hQ), div_div,
          div_le_iff₀ (mul_pos (by linarith : 0 < T) hQ), le_div_iff₀ h1pos]
        exact ⟨fun ⟨a, b⟩ => ⟨b.trans_eq (by ring), a⟩, fun ⟨a, b⟩ => ⟨b, a.trans_eq (by ring)⟩⟩
      change _ * (D.LamF T (γ : PG F)).indicator (D.kk k a (γ : PG F)) (ω,
                                                                        _) = _; rw [indicator_apply]
      by_cases hm : ((ω, fun v => pt (x v) (y v) (hy v)) : D.Y) ∈ D.LamF T (γ : PG F)
      · rw [ite_eq_left hm, ite_eq_left (hcond.1 hm), hkk (fun v => pt (x v) (y v) (hy v)),
            inv_mul_cancel_left₀ hc]; exact Finset.prod_congr rfl fun v _ => hφe v _ _ _
      · rw [ite_eq_right hm, ite_eq_right (mt hcond.2 hm), mul_zero])
    ((hC.1.const_mul (D.Te a g (D.rep ω))⁻¹).congr (ae_of_all _ fun _ => mul_smul_comm _ _ _))
  calc ∫ z, β0 (p z) • u z = D.Te a g (D.rep ω) * ∫ z : X I, β0 (p z) • ((D.Te a g (D.rep ω))⁻¹ * u z) := by
        rw [← integral_const_mul]; exact integral_congr_ae (ae_of_all _ fun z => by dsimp only; rw [mul_smul_comm, mul_inv_cancel_left₀ hc])
    _ = 0 := by rw [hF, mul_zero]

-- === F6: Unipotent terms contribution ===

theorem unipotent_terms_contribution_proof_jl : C1 → E0a → KernelTermsInvariantBounded → E0d → DiagonalTruncatedIntegralZero → F6 := by
  intro _ hE0a _ _ hF6b F I Gf ι _ _ _ _ D k a hH T hT γ ω hγ β hβ hint
  by_cases hTe : D.Te a γ.out (D.rep ω) = 0
  · have h0 z : (D.LamF T γ).indicator (D.kk k a γ) (ω,
                                                     z) = 0 := by rw [indicator_apply]; split_ifs <;> simp [Dat.kk, Dat.kt, hTe]
    simp [h0]
  obtain ⟨-, -, hP, -⟩ := hE0a F I Gf D hH.ax
  obtain ⟨i, hi⟩ := kk_supp D a γ ω hTe; obtain ⟨-, hdisc⟩ := kk_reg D k a hH γ ω i hi
  simp only [IsEll, not_forall, not_not] at hγ; obtain ⟨s, hs0, c, hc⟩ := hγ
  obtain ⟨δ1, hδ1⟩ := row_exists s hs0
  -- Diagonalize γ.out over F
  obtain ⟨δ0, h01, h10⟩ : ∃ δ : GL2 F, (δ * γ.out * δ⁻¹) 0 1 = 0 ∧ (δ * γ.out * δ⁻¹) 1 0 = 0 := by
    set h := δ1 * γ.out * δ1⁻¹
    have hv : ![0, 1] ᵥ* h.val = c • ![0, 1] := by
      simp only [h, Units.val_mul, ← vecMul_vecMul, hδ1, hc, smul_vecMul]
      rw [← hδ1, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
    have e10 : h 1 0 = 0 := by simpa [vecMul, dotProduct, Fin.sum_univ_two] using congrFun hv 0
    have htr : h.val.trace = γ.out.val.trace := by simp only [h,
                                                              Units.val_mul]; rw [trace_mul_cycle,
                                                                                  ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    have hdet : h.val.det = γ.out.val.det := by simp only [h, Units.val_mul,
                                                           det_mul]; rw [mul_right_comm, ← det_mul,
                                                                         ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, one_mul]
    have hne : h 0 0 - h 1 1 ≠ 0 := fun e => hdisc (by rw [← htr, ← hdet, trace_fin_two,
                                                           det_fin_two, e10]; linear_combination (h 0 0 - h 1 1) * e)
    set t : F :=
        h 0 1 / (h 0 0 - h 1 1); have ht : t * (h 0 0 - h 1 1) = h 0 1 := div_mul_cancel₀ _ hne
    let u : GL2 F := ⟨!![1, t; 0, 1], !![1, -t; 0, 1], by simp [one_fin_two], by simp [one_fin_two]⟩
    have hM : (u * δ1 * γ.out * (u * δ1)⁻¹).val = !![1, t; 0, 1] * !![h 0 0, h 0 1; 0,
                                                                      h 1 1] * !![1, -t; 0, 1] := by
      rw [show u * δ1 * γ.out * (u * δ1)⁻¹ = u * h * u⁻¹ by simp [h]; group, Units.val_mul,
          Units.val_mul, eta_fin_two h.val, e10]; rfl
    exact ⟨u * δ1, by rw [hM]; simp; linear_combination -ht, by rw [hM]; simp⟩
  -- Transport integral by δ0
  set δ : PG F := (δ0 : PG F)
  have hγ' : δ * γ * δ⁻¹ = ((δ0 * γ.out * δ0⁻¹ : GL2 F) : PG F) := by simp [δ]
  set p : D.Cj × D.Om := (γ, ω)
  have hmem (g : PG F) : g ∈ stabilizer (PG F) (δ • p) ↔ δ⁻¹ * g * δ ∈ stabilizer (PG F) p := by
    simp only [mem_stabilizer_iff, mul_smul]; rw [inv_smul_eq_iff]
  let φ : stabilizer (PG F) p ≃ stabilizer (PG F) (δ • p) :=
    ⟨fun x => ⟨δ * x * δ⁻¹, (hmem _).2 (by simp [show δ⁻¹ * (δ * (x : PG F) * δ⁻¹) * δ = x by group,
                                                 x.2])⟩,
     fun g => ⟨δ⁻¹ * g * δ, (hmem _).1 g.2⟩,
     fun x => Subtype.ext (by change δ⁻¹ * (δ * (x : PG F) * δ⁻¹) * δ = x; group),
     fun g => Subtype.ext (by change δ * (δ⁻¹ * (g : PG F) * δ) * δ⁻¹ = g; group)⟩
  let e := actEquiv_jl hP δ⁻¹
  have he : MeasurePreserving e volume volume := hP δ⁻¹
  have key w : β (e w) • (D.LamF T γ).indicator (D.kk k a γ) (ω, e w) =
      β (δ⁻¹ • w) • (D.LamF T (δ * γ * δ⁻¹)).indicator (D.kk k a (δ * γ * δ⁻¹)) (δ • ω, w) := by
    have hy : ((δ • ω, w) : D.Y) = δ • ((ω, δ⁻¹ • w) : D.Y) := by rw [Prod.smul_mk, smul_inv_smul]
    change β (δ⁻¹ • w) • (D.LamF T γ).indicator (D.kk k a γ) (ω, δ⁻¹ • w) = _; rw [hy]; congr 1
    have hL : δ • ((ω, δ⁻¹ • w) : D.Y) ∈ D.LamF T (δ * γ * δ⁻¹) ↔ ((ω,
                                                                    δ⁻¹ • w) : D.Y) ∈ D.LamF T γ :=
      ⟨fun h => by have := lamF_smul_jl D hH.ax T _ δ⁻¹ _ h; rwa [inv_smul_smul,
                                                                  show δ⁻¹ * (δ * γ * δ⁻¹) * δ⁻¹⁻¹ = γ by group] at this,
       lamF_smul_jl D hH.ax T γ δ _⟩
    by_cases hm : ((ω, δ⁻¹ • w) : D.Y) ∈ D.LamF T γ
    · rw [indicator_of_mem hm, indicator_of_mem (hL.2 hm), kk_conj D k a hH]
    · rw [indicator_of_notMem hm, indicator_of_notMem (mt hL.1 hm)]
  have hβ' : IsCut (stabilizer (PG F) ((((δ0 * γ.out * δ0⁻¹ : GL2 F) : PG F),
                                        δ • ω) : D.Cj × D.Om)) (fun w => β (δ⁻¹ • w)) := by
    rw [show ((((δ0 * γ.out * δ0⁻¹ : GL2 F) : PG F),
               δ • ω) : D.Cj × D.Om) = δ • p from Prod.ext hγ'.symm rfl]
    refine ⟨hβ.meas.comp (hP δ⁻¹).measurable, fun _ => hβ.nonneg _, fun w => ?_⟩
    rw [← φ.hasSum_iff]; convert hβ.sum (δ⁻¹ • w) using 2 with x
    change β (δ⁻¹ • (δ * (x : PG F) * δ⁻¹) • w) = β ((x : PG F) • δ⁻¹ • w)
    simp only [smul_smul, show δ⁻¹ * (δ * (x : PG F) * δ⁻¹) = (x : PG F) * δ⁻¹ by group]
  have hint' := (he.integrable_comp_emb e.measurableEmbedding).2 hint |>.congr (ae_of_all _ key)
  rw [hγ'] at hint'
  rw [← he.integral_comp' (fun z => β z • (D.LamF T γ).indicator (D.kk k a γ) (ω, z)),
      integral_congr_ae (ae_of_all _ key), hγ']
  exact hF6b F I Gf ι D k a hH T hT (δ0 * γ.out * δ0⁻¹) (δ • ω) h01 h10 _ hβ' hint'

-- === Fhyp ===

theorem pf_Fhyp_jl : C4 → E0a → KernelTermsInvariantBounded → E0d → E2 → E3 → Ecut → Fsum → F5 → F6 → Fhyp := by
  intro hC4 hE0a _ _ hE2 hE3 hEcut hFsum hF5 hF6 F I Gf ι _ _ _ _ D k a hyp b hb hint
  have hax := hyp.ax
  obtain ⟨hcnt, hsf, hpres, -⟩ := hE0a F I Gf D hax
  obtain ⟨-, hE2'⟩ := hE2 F I Gf ι D k a hyp
  have hb3 := hE3 F I Gf D hax b hb
  obtain ⟨C, hC⟩ := hF5 F I Gf ι D k a hyp
  have : Countable (PG F) := hcnt; have : Countable D.Cj := hcnt; have : Countable D.Om := hax.cO
  have hbI : Integrable b D.μY := ⟨hb.meas.aestronglyMeasurable,
                                   (lintegral_congr fun y => Real.enorm_eq_ofReal (hb.nonneg y)).trans_lt hb3⟩
  let uT (T : ℝ) (γ : PG F) (y : D.Y) : ℂ :=
      if IsEll γ then 0 else (D.LamF T γ).indicator (D.kk k a γ) y
  have hsumle T (hT : 1 < T) y (hy : y ∉ D.abelian₂ T) : ∑' γ, ‖uT T γ y‖ₑ ≤ C :=
    (ENNReal.tsum_le_tsum fun γ => by dsimp only [uT]; split_ifs <;> simp).trans ((hC T hT y).2 hy)
  have hon T (hT : 1 < T) y (hy : y ∈ D.abelian₂ T) γ : uT T γ y = if IsEll γ then 0 else D.kk k a γ y := by
    dsimp only [uT]; split_ifs; rfl; exact indicator_of_mem ((hC T hT y).1 hy γ) _
  have step1 T (hT : 1 < T) : Integrable (fun y => b y • ∑' γ,
                                          uT T γ y) D.μY ∧ ∫ y, b y • ∑' γ, uT T γ y ∂D.μY = 0 := by
    obtain ⟨CT, hCT⟩ := hE2' T
    have hfin : ∫⁻ y, oR (b y) * ∑' γ, ‖uT T γ y‖ₑ ∂D.μY < ∞ := by
      have hle y : ∑' γ, ‖uT T γ y‖ₑ ≤ (CT : ℝ≥0∞) + C := by
        by_cases hy : y ∈ D.abelian₂ T
        · exact ((ENNReal.tsum_le_tsum fun γ => by dsimp only [uT]; split_ifs; simp; rw [indicator_apply]; split_ifs <;> simp).trans (hCT y hy)).trans le_self_add
        · exact (hsumle T hT y hy).trans le_add_self
      exact ((lintegral_mono fun y => by gcongr; exact hle y).trans_eq (lintegral_mul_const' _ _ (by simp))).trans_lt (ENNReal.mul_lt_top hb3 (by simp))
    obtain ⟨hb', hFs⟩ := hFsum F I Gf D hax b hb
    obtain ⟨hm', hi', hiY, heq⟩ := hFs (uT T) (fun γ => by by_cases h : IsEll γ <;> simp [uT, h,
                                                                                          (meas_kk D k a hyp γ).indicator (meas_lamF_jl D hax T γ)]) hfin
    refine ⟨hiY, heq.trans ?_⟩
    obtain ⟨f, -, -, hR⟩ := orbit_reps (G := PG F) (α := D.Cj × D.Om)
    choose β hβ using fun r : D.Cj × D.Om => (hEcut F I Gf D hax).2 r.2 (stabilizer (PG F) r) fun g hg => congrArg Prod.snd (mem_stabilizer_iff.1 hg)
    have hinv' (g : PG F) (p : (D.Cj × D.Om) × D.Xs) : uT T (D.el (g • p).1.1) ((g • p).1.2,
                                                                                (g • p).2) = uT T (D.el p.1.1) (p.1.2, p.2) := by
      rcases p with ⟨⟨γ, ω⟩, z⟩; show uT T (g * D.el γ * g⁻¹) (g • ((ω,
                                                                     z) : D.Y)) = uT T (D.el γ) (ω,
                                                                                                 z)
      dsimp only [uT]; rw [isEll_conj_jl]; split_ifs; rfl
      rw [indicator_apply, indicator_apply, kk_conj D k a hyp]
      have hL : g • ((ω, z) : D.Y) ∈ D.LamF T (g * D.el γ * g⁻¹) ↔ ((ω,
                                                                     z) : D.Y) ∈ D.LamF T (D.el γ) :=
        ⟨fun h => by have := lamF_smul_jl D hax T _ g⁻¹ _ h; rwa [inv_smul_smul,
                                                                  show g⁻¹ * (g * D.el γ * g⁻¹) * g⁻¹⁻¹ = D.el γ by group] at this, lamF_smul_jl D hax T _ g _⟩
      simp only [hL]
    obtain ⟨hI,
            hS⟩ := hC4 (PG F) (D.Cj × D.Om) D.Xs volume hpres _ hb' _ hm' hinv' hi' (range f) hR β fun r _ => hβ r
    have hz (r : range f) : ∫ x, β r x • uT T (D.el r.1.1) (r.1.2, x) = 0 := by
      by_cases he : IsEll (D.el r.1.1)
      · simp [uT, he]
      · simp only [uT, he, ite_false]
        exact hF6 F I Gf ι D k a hyp T hT (D.el r.1.1) r.1.2 he (β r.1) (hβ r.1) (by simpa only [uT,
                                                                                                 he, ite_false] using hI r.1 r.2)
    simp only [hz] at hS; exact hS.unique hasSum_zero
  have hT2 (n : ℕ) : (1 : ℝ) < (n : ℝ) + 2 := by linarith [n.cast_nonneg (α := ℝ)]
  have hlim : Tendsto (fun n : ℕ => ∫ y, b y • ∑' γ, uT ((n : ℝ) + 2) γ y ∂D.μY) atTop
      (𝓝 (∫ y, b y • (∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) ∂D.μY)) :=
    tendsto_integral_of_dominated_convergence (fun y => ‖b y • ∑' γ : PG F,
                                               (if IsEll γ then 0 else D.kk k a γ y)‖ + b y * C)
      (fun n => (step1 _ (hT2 n)).1.aestronglyMeasurable) (hint.norm.add (hbI.mul_const _))
      (fun n => ae_of_all _ fun y => by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (hb.nonneg y), ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ (hb.nonneg y)
        by_cases hy : y ∈ D.abelian₂ ((n : ℝ) + 2)
        · rw [tsum_congr (hon _ (hT2 n) y hy)]; exact le_add_of_nonneg_right C.2
        · exact (by simpa using ENNReal.toReal_mono ENNReal.coe_ne_top (enorm_tsum_le_tsum_enorm.trans (hsumle _ (hT2 n) y hy)) : ‖∑' γ, uT ((n : ℝ) + 2) γ y‖ ≤ C).trans (le_add_of_nonneg_left (norm_nonneg _)))
      (ae_of_all _ fun y => by
        obtain ⟨T₀, hT₀⟩ := htY_bdd D hax y; obtain ⟨N, hN⟩ := exists_nat_ge T₀
        exact tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => by
          dsimp only; rw [tsum_congr (hon _ (hT2 n) y (hT₀ _ (by have : (N : ℝ) ≤ n := (by exact_mod_cast hn); linarith)))]⟩))
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (Eventually.of_forall fun n => (step1 _ (hT2 n)).2.symm))

-- === TF: Final Trace Formula ===

theorem pf_TF_jl : E2 → Ecut → E6 → Fell → Fhyp → TF := by
  intro hE2 hcut hE6 hFell hFhyp F I Gf _ _ _ D hAx ι _ a
  obtain ⟨S, hFam, hS⟩ := hFell F I Gf D hAx ι a
  refine ⟨S, hFam, fun k hH hfd h => ?_⟩
  obtain ⟨⟨b, hb⟩, -⟩ := hcut F I Gf D hAx
  obtain ⟨hi, htr⟩ := hE6 F I Gf ι D k a hH hfd h b hb
  obtain ⟨hie, hge⟩ := hS k hH b hb
  have hsplit y : ∑' γ : PG F, D.kk k a γ y = (∑' γ : PG F,
                                               if IsEll γ then D.kk k a γ y else 0) + ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y := by
    have hf := (hE2 F I Gf ι D k a hH).1 y
    rw [← Summable.tsum_add (Summable.of_norm_bounded hf fun _ => by split_ifs <;> simp) (Summable.of_norm_bounded hf fun _ => by split_ifs <;> simp)]
    exact tsum_congr fun _ => by split_ifs <;> simp
  have hih : Integrable (fun y => b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) D.μY :=
    (hi.sub hie).congr (ae_of_all _ fun y => by simp only [Pi.sub_apply]; rw [hsplit y, smul_add,
                                                                              add_sub_cancel_left])
  rw [htr, ← hge, show (fun y => b y • ∑' γ : PG F, D.kk k a γ y) = fun y => b y • (∑' γ : PG F,
                                                                                    if IsEll γ then D.kk k a γ y else 0) +
      b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y from funext fun y => by rw [hsplit y,
                                                                                         smul_add],
    integral_add hie hih, hFhyp F I Gf ι D k a hH b hb hih, add_zero]

end UpperTheory.Esk

-- ==== Solution

namespace UpperTheory.Esk

theorem half_plane_measure_invariant_holds : B1a := half_plane_measure_invariant_proof_jl
theorem automorphy_factor_kernel_algebra_holds : B1b := automorphy_factor_kernel_algebra_proof_jl
theorem kernel_terms_invariant_bounded_holds : KernelTermsInvariantBounded :=
    kernel_terms_invariant_bounded_proof_jl half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds
theorem heights_on_quotient_holds : E0d :=
    heights_on_quotient_proof_jl half_plane_measure_invariant_holds
theorem hyperbolic_kappa_properties_holds : B1c := hyperbolic_kappa_properties_proof_jl
theorem actions_preserve_measures_holds : E0a :=
    actions_preserve_measures_proof_jl half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds
theorem s_Pack : Pack :=
    pf_Pack_jl automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds actions_preserve_measures_holds
theorem s_Mult : Mult := pf_Mult_jl automorphy_factor_kernel_algebra_holds heights_on_quotient_holds
theorem upper_half_plane_coordinates_holds : UpperHalfPlaneMeasureCoordinates :=
    upper_half_plane_measure_coordinates_jl
theorem hyperbolic_ball_volume_holds : B6 :=
    hyperbolic_ball_volume_proof_jl half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds upper_half_plane_coordinates_holds
theorem s_KapInt : KapInt :=
    pf_KapInt_jl half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds hyperbolic_ball_volume_holds
theorem s_KapSum : KapSum := pf_KapSum_jl s_Pack s_Mult s_KapInt
theorem kernel_sum_bounded_holds : E2 :=
    kernel_sum_bounded_proof_jl kernel_terms_invariant_bounded_holds heights_on_quotient_holds s_KapSum
theorem orbit_cover_holds : C2 := orbit_cover_proof_jl
theorem s_Ecut : Ecut :=
    pf_Ecut_jl automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds orbit_cover_holds actions_preserve_measures_holds heights_on_quotient_holds s_KapSum
theorem forms_stable_under_operators_holds : FormsStableUnderOperators :=
    forms_stable_under_operators_proof_jl
theorem cusp_region_volume_finite_holds : E3 :=
    cusp_region_volume_finite_proof_jl half_plane_measure_invariant_holds upper_half_plane_coordinates_holds orbit_cover_holds actions_preserve_measures_holds heights_on_quotient_holds
theorem kernel_level_transform_holds : E4 :=
    kernel_level_transform_proof_jl half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds heights_on_quotient_holds s_KapSum s_KapInt
theorem kernel_inverse_symmetry_holds : faceMap_zero_comp_eq_one :=
    kernel_inverse_symmetry_jl half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds actions_preserve_measures_holds heights_on_quotient_holds s_KapSum
theorem inverse_series_summable_holds : C3 := inverse_series_summable_jl
theorem cayley_transform_holds : B2 := cayley_transform_proof_jl
theorem reproducing_formula_holds_alt : B3 :=
    reproducing_formula_proof_jl half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds cayley_transform_holds hyperbolic_ball_volume_holds
theorem multivariable_reproducing_formula_holds : MultivariableReproducingFormula :=
    multivariable_reproducing_formula_proof_jl half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds reproducing_formula_holds_alt s_KapInt
theorem reproducing_kernel_expansion_holds : E5 :=
    e5_of_reproducing_formula_jl automorphy_factor_kernel_algebra_holds inverse_series_summable_holds actions_preserve_measures_holds kernel_inverse_symmetry_holds multivariable_reproducing_formula_holds
theorem s_LinTr : LinTr := pf_LinTr_jl
theorem linear_trace_identity_holds : E6 :=
    e6_of_linear_trace_identity_jl actions_preserve_measures_holds forms_stable_under_operators_holds kernel_terms_invariant_bounded_holds cusp_region_volume_finite_holds kernel_level_transform_holds kernel_inverse_symmetry_holds reproducing_kernel_expansion_holds s_LinTr
theorem action_integral_swap_holds : C1 := action_integral_swap_proof_jl
theorem counting_measure_invariance_holds : C4 :=
    counting_measure_invariance_proof_jl action_integral_swap_holds
theorem kernel_series_converges_holds : E1 :=
    kernel_series_converges_proof_jl automorphy_factor_kernel_algebra_holds kernel_terms_invariant_bounded_holds heights_on_quotient_holds s_Pack s_Mult s_KapInt
theorem s_Fsum : Fsum := pf_Fsum_jl actions_preserve_measures_holds
theorem diagonal_integrand_vanishes_holds : DiagonalIntegrandVanishes :=
    diagonal_integrand_vanishes_proof_jl
theorem s_Fcen : Fcen := pf_Fcen_jl
theorem diagonal_terms_contribution_holds : F2 :=
    diagonal_terms_contribution_proof_jl half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds upper_half_plane_coordinates_holds diagonal_integrand_vanishes_holds action_integral_swap_holds actions_preserve_measures_holds kernel_terms_invariant_bounded_holds s_Ecut s_Fcen
theorem radial_integral_formula_holds : B4 :=
    radial_integral_formula_proof_jl half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds cayley_transform_holds hyperbolic_ball_volume_holds
theorem elliptic_terms_contribution_holds : F3 :=
    elliptic_terms_contribution_proof_jl half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds radial_integral_formula_holds action_integral_swap_holds actions_preserve_measures_holds kernel_terms_invariant_bounded_holds heights_on_quotient_holds s_Mult s_Fcen
theorem imaginary_part_bound_holds : F4 :=
    imaginary_part_bound_proof_jl automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds heights_on_quotient_holds s_Mult
theorem s_Fell : Fell :=
    pf_Fell_jl counting_measure_invariance_holds actions_preserve_measures_holds kernel_terms_invariant_bounded_holds heights_on_quotient_holds kernel_series_converges_holds cusp_region_volume_finite_holds s_Ecut s_Fsum diagonal_terms_contribution_holds elliptic_terms_contribution_holds imaginary_part_bound_holds
theorem kernel_trace_bound_holds : F5 :=
    kernel_trace_bound_proof_jl heights_on_quotient_holds kernel_series_converges_holds
theorem unipotent_integrand_vanishes_holds : ConstantTermVanishingAlt :=
    unipotent_integrand_vanishes_proof_jl half_plane_measure_invariant_holds upper_half_plane_coordinates_holds
theorem unipotent_truncated_integral_holds : DiagonalTruncatedIntegralZero :=
    diagonal_truncated_integral_zero_jl half_plane_measure_invariant_holds upper_half_plane_coordinates_holds diagonal_integrand_vanishes_holds action_integral_swap_holds actions_preserve_measures_holds kernel_terms_invariant_bounded_holds heights_on_quotient_holds s_Ecut s_Fcen unipotent_integrand_vanishes_holds
theorem unipotent_terms_contribution_holds : F6 :=
    unipotent_terms_contribution_proof_jl action_integral_swap_holds actions_preserve_measures_holds kernel_terms_invariant_bounded_holds heights_on_quotient_holds unipotent_truncated_integral_holds
theorem s_Fhyp : Fhyp :=
    pf_Fhyp_jl counting_measure_invariance_holds actions_preserve_measures_holds kernel_terms_invariant_bounded_holds heights_on_quotient_holds kernel_sum_bounded_holds cusp_region_volume_finite_holds s_Ecut s_Fsum kernel_trace_bound_holds unipotent_terms_contribution_holds
theorem s_TF : TF :=
    pf_TF_jl kernel_sum_bounded_holds s_Ecut linear_trace_identity_holds s_Fell s_Fhyp

theorem s_Sys : Sys := pf_Sys
theorem finite_system_holds : Fin0 := finite_system_proof s_Sys
theorem s_Osg : Osg := pf_Osg

end UpperTheory.Esk


end
