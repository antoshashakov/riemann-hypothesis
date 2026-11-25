module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.AbsMax

@[expose] public section

open Complex Filter Metric Topology

noncomputable section

namespace Formalism.ZF.LocalZeroFactorizationBounds

theorem logDeriv_product (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z - ρ ≠ 0) :
    logDeriv (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) z = ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
  rw [logDeriv_fun_prod (f := fun ρ w => (w - ρ) ^ m ρ)
    (fun ρ hρ => pow_ne_zero (m ρ) (hz ρ hρ))
    (fun ρ _ => (differentiableAt_id.sub_const ρ).pow (m ρ))]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [logDeriv_fun_pow (f := fun w => w - ρ) (differentiableAt_id.sub_const ρ), logDeriv_apply]
  change (m ρ : ℂ) * (deriv (fun w => id w - ρ) z / _) = _
  rw [deriv_sub_const, deriv_id, mul_one_div]

theorem bounds_of_factorization (hlog : LogDerivBound) {f h : ℂ → ℂ} {z₀ : ℂ} {r M : ℝ}
    (hr : 0 < r) (hM : 1 ≤ M) (Z : Finset ℂ) (m : ℂ → ℕ)
    (hZ : ∀ ρ ∈ Z, ρ ∈ closedBall z₀ (r / 3) ∧ f ρ = 0)
    (hh : DifferentiableOn ℂ h (closedBall z₀ r))
    (hh0 : ∀ z ∈ closedBall z₀ (r / 3), h z ≠ 0)
    (hfac : ∀ z ∈ closedBall z₀ r, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z)
    (hbound : ∀ z ∈ closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖) :
    ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 ∧
    ∀ z ∈ closedBall z₀ (r / 6), f z ≠ 0 →
      ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log M / r := by
  let P (w : ℂ) := ∏ ρ ∈ Z, (w - ρ) ^ m ρ
  let N : ℕ := ∑ ρ ∈ Z, m ρ
  have hr3 : 0 < r / 3 := by positivity
  have hP₀ : ‖P z₀‖ ≤ (r / 3) ^ N := by
    dsimp only [P, N]
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun ρ _ => norm_nonneg _) fun ρ hρ => ?_
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (by simpa only [mem_closedBall, dist_comm ρ z₀, dist_eq_norm] using (hZ ρ hρ).1) _
  have hPw (w : ℂ) (hw : w ∈ sphere z₀ r) : (2 * (r / 3)) ^ N ≤ ‖P w‖ := by
    dsimp only [P, N]
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun ρ _ => pow_nonneg (by positivity) _) fun ρ hρ => ?_
    rw [norm_pow, ← dist_eq_norm]
    have hρdist := mem_closedBall.mp (hZ ρ hρ).1
    have hwdist := mem_sphere.mp hw
    exact pow_le_pow_left₀ (by positivity) (by linarith [dist_triangle w ρ z₀]) _
  have hc : z₀ ∈ closedBall z₀ r := mem_closedBall_self hr.le
  have hmax (z : ℂ) (hz : z ∈ closedBall z₀ r) : ‖h z‖ ≤ M * ‖h z₀‖ / (2 : ℝ) ^ N := by
    have hD : DiffContOnCl ℂ h (ball z₀ r) :=
      DifferentiableOn.diffContOnCl (by rwa [closure_ball z₀ hr.ne'])
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hD ?_
      (by rwa [closure_ball z₀ hr.ne'])
    intro w hw
    rw [frontier_ball z₀ hr.ne'] at hw
    have hwc := sphere_subset_closedBall hw
    apply (le_div_iff₀ (by positivity)).mpr
    apply le_of_mul_le_mul_left _ (pow_pos hr3 N)
    calc (r / 3) ^ N * (‖h w‖ * (2 : ℝ) ^ N) = (2 * (r / 3)) ^ N * ‖h w‖ := by
          rw [mul_pow]
          ring
      _ ≤ ‖P w‖ * ‖h w‖ := mul_le_mul_of_nonneg_right (hPw w hw) (norm_nonneg _)
      _ = ‖f w‖ := by rw [hfac w hwc, norm_mul]
      _ ≤ M * ‖f z₀‖ := hbound w hwc
      _ = M * (‖P z₀‖ * ‖h z₀‖) := by rw [hfac z₀ hc, norm_mul]
      _ ≤ M * ((r / 3) ^ N * ‖h z₀‖) := by gcongr
      _ = (r / 3) ^ N * (M * ‖h z₀‖) := by ring
  have h2M : (2 : ℝ) ^ N ≤ M := by
    have hpositive : 0 < ‖h z₀‖ := norm_pos_iff.mpr (hh0 z₀ (mem_closedBall_self hr3.le))
    have hcenter := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ N)).mp (hmax z₀ hc)
    exact le_of_mul_le_mul_left (by simpa only [mul_comm M] using hcenter) hpositive
  refine ⟨?_, ?_⟩
  · change (N : ℝ) ≤ _
    rw [le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_pow]
    exact Real.log_le_log (by positivity) h2M
  · intro z hz hfz
    have hznhds : closedBall z₀ r ∈ 𝓝 z := by
      apply Filter.mem_of_superset (isOpen_ball.mem_nhds ?_) ball_subset_closedBall
      rw [mem_ball]
      linarith [mem_closedBall.mp hz]
    have hev : f =ᶠ[𝓝 z] fun w => P w * h w :=
      Filter.mem_of_superset hznhds fun w hw => hfac w hw
    have hzρ (ρ : ℂ) (hρ : ρ ∈ Z) : z - ρ ≠ 0 :=
      fun hzero => hfz (sub_eq_zero.mp hzero ▸ (hZ ρ hρ).2)
    have hPne : P z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hzρ ρ hρ)
    have hhne := hh0 z (closedBall_subset_closedBall (by linarith) hz)
    have hPd : DifferentiableAt ℂ P z :=
      DifferentiableAt.fun_finsetProd fun ρ _ => (differentiableAt_id.sub_const ρ).pow (m ρ)
    have hs := logDeriv_fun_mul z hPne hhne hPd (hh.differentiableAt hznhds)
    rw [← (logDeriv_congr_nhds hev).self_of_nhds, logDeriv_product Z m z hzρ] at hs
    change ‖logDeriv f z - _‖ ≤ _
    rw [hs, add_sub_cancel_left]
    have hbound_h (w : ℂ) (hw : w ∈ closedBall z₀ (r / 3)) : ‖h w‖ ≤ M * ‖h z₀‖ :=
      (hmax w (closedBall_subset_closedBall (by linarith) hw)).trans
        (div_le_self (by positivity) (one_le_pow₀ one_le_two))
    have hlocal := hlog h z₀ (r / 3) M hr3 hM
      (hh.mono (closedBall_subset_closedBall (by linarith))) hh0 hbound_h
    have hz' : z ∈ closedBall z₀ (r / 3 / 2) := by
      simpa only [show r / 3 / 2 = r / 6 by ring] using hz
    calc ‖logDeriv h z‖ ≤ 24 * Real.log M / (r / 3) := hlocal z hz'
      _ = 72 * Real.log M / r := by rw [div_div_eq_mul_div]; ring

end Formalism.ZF.LocalZeroFactorizationBounds
