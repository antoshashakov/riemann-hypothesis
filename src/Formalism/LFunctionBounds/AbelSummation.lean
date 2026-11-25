module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormCpowSubLePoint

@[expose] public section

open Complex Filter Topology

noncomputable section

namespace Formalism.LFunctionBounds.AbelSummation

variable (f : ℕ → ℂ)

def Ap (n : ℕ) : ℂ := ∑ k ∈ Finset.Icc 1 n, f k

def dterm (s : ℂ) (n : ℕ) : ℂ := Ap f n * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s))

def G (s : ℂ) : ℂ := ∑' n, dterm f s n

lemma Ap_zero : Ap f 0 = 0 := by
  simp [Ap]

lemma Ap_succ (n : ℕ) : Ap f (n + 1) = Ap f n + f (n + 1) := by
  unfold Ap
  exact Finset.sum_Icc_succ_top (by omega) f

lemma dterm_zero (s : ℂ) : dterm f s 0 = 0 := by
  rw [dterm, Ap_zero, zero_mul]

lemma norm_dterm_le {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖dterm f s n‖ ≤ B * (‖s‖ * (n : ℝ) ^ (-s.re - 1)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [dterm_zero, norm_zero]
    exact mul_nonneg hB0 (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · have hx : (0 : ℝ) < n := by exact_mod_cast hn
    have key : ‖(n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
      simpa using Formalism.ZF.ComplexPowerDifferenceIntegral.norm_cpow_sub_le_point
        hx le_rfl (le_add_of_nonneg_right zero_le_one) hs
    show ‖Ap f n * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s))‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hB n) key (norm_nonneg _) hB0

lemma summable_norm_dterm {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n => ‖dterm f s n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (norm_dterm_le f hB hs) ?_
  exact ((Real.summable_nat_rpow.mpr (by linarith)).mul_left ‖s‖).mul_left B

lemma summable_dterm {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Summable (dterm f s) := (summable_norm_dterm f hB hs).of_norm

lemma partial_identity (s : ℂ) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), dterm f s n + Ap f M * ((M : ℂ) + 1) ^ (-s) =
      ∑ n ∈ Finset.Icc 1 M, f n * (n : ℂ) ^ (-s) := by
  induction M with
  | zero => simp [dterm_zero, Ap_zero]
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ← ih]
    simp only [dterm]
    rw [Ap_succ]
    push_cast
    ring

lemma G_differentiableOn {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) :
    DifferentiableOn ℂ (G f) {s : ℂ | 0 < s.re} := by
  intro s0 hs0
  have hs0' : 0 < s0.re := hs0
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hUo : IsOpen ({s : ℂ | s0.re / 2 < s.re} ∩ Metric.ball 0 (‖s0‖ + 1)) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hs0U : s0 ∈ {s : ℂ | s0.re / 2 < s.re} ∩ Metric.ball 0 (‖s0‖ + 1) := by
    refine ⟨?_, ?_⟩
    · show s0.re / 2 < s0.re
      linarith
    · simp
  have hdiff : DifferentiableOn ℂ (fun w => ∑' n, dterm f w n)
      ({s : ℂ | s0.re / 2 < s.re} ∩ Metric.ball 0 (‖s0‖ + 1)) := by
    apply Complex.differentiableOn_tsum_of_summable_norm (F := fun n w => dterm f w n)
      (u := fun n : ℕ => B * ((‖s0‖ + 1) * (n : ℝ) ^ (-(s0.re / 2) - 1)))
    · exact ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _).mul_left _
    · intro n w hw
      have h1 : s0.re / 2 < w.re := hw.1
      have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at h1; linarith
      apply DifferentiableAt.differentiableWithinAt
      show DifferentiableAt ℂ (fun w => Ap f n * ((n : ℂ) ^ (-w) - ((n : ℂ) + 1) ^ (-w))) w
      apply DifferentiableAt.const_mul
      apply DifferentiableAt.sub
      · exact (differentiableAt_id.neg).const_cpow (Or.inr (neg_ne_zero.mpr hw0))
      · exact (differentiableAt_id.neg).const_cpow (Or.inr (neg_ne_zero.mpr hw0))
    · exact hUo
    · intro n w hw
      have h1 : s0.re / 2 < w.re := hw.1
      have h2 : ‖w‖ < ‖s0‖ + 1 := by simpa using hw.2
      have hwre : 0 < w.re := by linarith
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · show ‖dterm f w 0‖ ≤ B * ((‖s0‖ + 1) * ((0 : ℕ) : ℝ) ^ (-(s0.re / 2) - 1))
        rw [dterm_zero, norm_zero]
        exact mul_nonneg hB0 (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · show ‖dterm f w n‖ ≤ B * ((‖s0‖ + 1) * (n : ℝ) ^ (-(s0.re / 2) - 1))
        refine (norm_dterm_le f hB hwre n).trans ?_
        apply mul_le_mul_of_nonneg_left _ hB0
        apply mul_le_mul h2.le _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn) (by linarith)
  exact (hdiff.differentiableAt (hUo.mem_nhds hs0U)).differentiableWithinAt

lemma partial_tendsto_G {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, f n * (n : ℂ) ^ (-s)) atTop
      (𝓝 (G f s)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have h1 : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (M + 1), dterm f s n) atTop (𝓝 (G f s)) :=
    ((summable_dterm f hB hs).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun M : ℕ => Ap f M * ((M : ℂ) + 1) ^ (-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hg : Tendsto (fun M : ℕ => ((M : ℝ) + 1) ^ (-s.re)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hs).comp
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    have hg' := hg.const_mul B
    rw [mul_zero] at hg'
    refine squeeze_zero (fun M => norm_nonneg _) (fun M => ?_) hg'
    show ‖Ap f M * ((M : ℂ) + 1) ^ (-s)‖ ≤ B * ((M : ℝ) + 1) ^ (-s.re)
    have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    rw [norm_mul, show ((M : ℂ) + 1) = (((M : ℝ) + 1 : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hM, Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hB M) (Real.rpow_nonneg hM.le _)
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact h3.congr (partial_identity f s)

end Formalism.LFunctionBounds.AbelSummation
