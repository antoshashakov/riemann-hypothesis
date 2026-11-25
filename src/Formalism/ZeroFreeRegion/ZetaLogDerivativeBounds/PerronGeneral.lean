module

public import Formalism.ZetaNonvanishing.MellinSgen
public import Mathlib.Analysis.MellinInversion
public import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism.PerronGeneral

def kernel (g : ℂ → ℂ) (y : ℝ) (w : ℂ) : ℂ :=
  g w * (y : ℂ) ^ w / (w * (w - 1))

lemma continuous_lseries_kernel {f : ℕ → ℂ} (hf : ∀ s : ℂ, 1 < s.re → LSeriesSummable f s)
    {y σ : ℝ} (hy : 0 < y) (hσ : 1 < σ) :
    Continuous (fun t : ℝ => kernel (LSeries f) y ((σ : ℂ) + t * I)) := by
  have hA := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    (fun r hr => hf r (by simpa using hr))
  have hline : Continuous (fun t : ℝ => (σ : ℂ) + t * I) := by fun_prop
  have hmem (t : ℝ) : LSeries.abscissaOfAbsConv f < ((σ : ℂ) + t * I).re :=
    hA.trans_lt (EReal.coe_lt_coe_iff.mpr (by simpa using hσ))
  have hL := (LSeries_differentiableOn f).continuousOn.comp_continuous hline hmem
  refine (hL.mul (hline.const_cpow (Or.inl (ofReal_ne_zero.mpr hy.ne')))).div
    (hline.mul (hline.sub continuous_const)) fun t => ?_
  exact mul_ne_zero (Complex.ne_zero_of_re_pos (by simpa using zero_lt_one.trans hσ))
    (Complex.ne_zero_of_re_pos (by simpa using sub_pos.mpr hσ))

lemma norm_lseries_le_of_re_eq {f a : ℕ → ℂ} {w s : ℂ} (hs : LSeriesSummable a s)
    (hw : w.re = s.re) (h : ∀ n, ‖f n‖ ≤ ‖a n‖) :
    ‖LSeries f w‖ ≤ ∑' n, ‖LSeries.term a s n‖ := by
  have hterm (n : ℕ) : ‖LSeries.term f w n‖ ≤ ‖LSeries.term a s n‖ := by
    refine (LSeries.norm_term_le w (h n)).trans_eq ?_
    simp only [LSeries.norm_term_eq, hw]
  have hsum := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hs.norm
  exact (norm_tsum_le_tsum_norm hsum).trans (Summable.tsum_le_tsum hterm hsum hs.norm)

lemma integrable_kernel {g : ℂ → ℂ} {y σ B : ℝ} (hy : 0 < y) (hσ : 1 < σ)
    (hc : Continuous (fun t : ℝ => kernel g y ((σ : ℂ) + t * I)))
    (bound : ∀ t : ℝ, ‖g ((σ : ℂ) + t * I)‖ ≤ B)
    (denom : ∀ t : ℝ, min ((σ - 1) ^ 2) 1 * (1 + t ^ 2) ≤
      ‖((σ : ℂ) + t * I) * (((σ : ℂ) + t * I) - 1)‖) :
    Integrable (fun t : ℝ => kernel g y ((σ : ℂ) + t * I)) := by
  let d := min ((σ - 1) ^ 2) 1
  have hd : 0 < d := lt_min (by nlinarith) one_pos
  have hB : 0 ≤ B := (norm_nonneg _).trans (bound 0)
  have hy' : 0 ≤ y ^ σ := Real.rpow_nonneg hy.le _
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (B * y ^ σ / d))
    hc.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [kernel, norm_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hy,
    show ((σ : ℂ) + t * I).re = σ by simp]
  have hpos : 0 < d * (1 + t ^ 2) := by positivity
  calc _ ≤ B * y ^ σ / (d * (1 + t ^ 2)) :=
        div_le_div₀ (mul_nonneg hB hy') (mul_le_mul_of_nonneg_right (bound t) hy') hpos (denom t)
    _ = _ := by field_simp

private lemma neg_vertical (σ t : ℝ) :
    ((-σ : ℝ) : ℂ) + t * I = -((σ : ℂ) + ((-t : ℝ) : ℂ) * I) := by
  push_cast
  ring

lemma vertical_integrable {g : ℂ → ℂ} {F : ℝ → ℂ} {σ : ℝ} (hσ : 1 < σ)
    (heq : ∀ w : ℂ, 1 < w.re → mellin F (-w) = g w / (w * (w - 1)))
    (hi : Integrable (fun t : ℝ => kernel g 1 ((σ : ℂ) + t * I))) :
    VerticalIntegrable (mellin F) (-σ) := by
  refine hi.comp_neg.congr (Eventually.of_forall fun t => ?_)
  show kernel g 1 ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) =
    mellin F (((-σ : ℝ) : ℂ) + t * I)
  rw [neg_vertical, heq _ (by simp [hσ])]
  simp [kernel]

lemma mellin_inversion {g : ℂ → ℂ} {F : ℝ → ℂ} {y σ : ℝ} (hy : 0 < y) (hσ : 1 < σ)
    (heq : ∀ w : ℂ, 1 < w.re → mellin F (-w) = g w / (w * (w - 1)))
    (hm : MellinConvergent F (-σ : ℝ)) (hv : VerticalIntegrable (mellin F) (-σ))
    (hc : ContinuousAt F y) :
    F y = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, kernel g y ((σ : ℂ) + t * I) := by
  rw [← mellinInv_mellin_eq (-σ) F hy hm hv hc, mellinInv, Complex.real_smul]
  push_cast
  congr 1
  rw [← integral_neg_eq_self (fun t : ℝ => kernel g y ((σ : ℂ) + t * I)) volume]
  congr 1
  funext t
  rw [← ofReal_neg, neg_vertical, heq _ (by simp [hσ]), neg_neg, smul_eq_mul]
  unfold kernel
  ring

lemma mellin_convergent_of_support {F : ℝ → ℂ} {σ : ℝ}
    (hzero : ∀ x ≤ 1, F x = 0)
    (hi : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(σ : ℂ) - 1) • F x) (Ioi 1)) :
    MellinConvergent F (-σ : ℝ) := by
  unfold MellinConvergent
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ (by simpa only [Complex.ofReal_neg] using hi)
  refine integrableOn_zero.congr_fun (fun x hx => ?_) measurableSet_Ioc
  simp [hzero x hx.2]

lemma perron_continuous_mxS (n : ℕ) : Continuous (Formalism.mxS n) := by
  show Continuous (fun x : ℝ => max (x / n - 1) 0)
  exact ((continuous_id.div_const _).sub continuous_const).max continuous_const

lemma summatory_eq_sum_range {a : ℕ → ℝ} (ha0 : a 0 = 0) {N : ℕ} {x : ℝ} (hx : x < N) :
    Formalism.Sa a x = ∑ n ∈ Finset.range N, a n * Formalism.mxS n x := by
  rw [Formalism.Sa_eq_tsum _ ha0]
  refine tsum_eq_sum (fun n hn => ?_)
  rw [Finset.mem_range, not_lt] at hn
  have hxn : x < n := lt_of_lt_of_le hx (by exact_mod_cast hn)
  refine Formalism.a_mxS_eq_zero _ ha0 x n ?_
  rw [Finset.mem_Icc]
  rintro ⟨h1, h2⟩
  have hx1 : 1 ≤ x := Nat.floor_pos.mp (by omega)
  have : (n : ℝ) ≤ x := (Nat.cast_le.mpr h2).trans (Nat.floor_le (by linarith))
  linarith

lemma summatory_function_continuousAt {a : ℕ → ℝ} (ha0 : a 0 = 0) (y : ℝ) :
    ContinuousAt (fun x => (Formalism.Sa a x : ℂ)) y := by
  obtain ⟨N, hN⟩ := exists_nat_gt y
  have hev : (fun x => ((∑ n ∈ Finset.range N, a n * Formalism.mxS n x : ℝ) : ℂ)) =ᶠ[𝓝 y]
      (fun x => (Formalism.Sa a x : ℂ)) := by
    filter_upwards [eventually_lt_nhds hN] with x hx
    rw [summatory_eq_sum_range ha0 hx]
  refine ContinuousAt.congr ?_ hev
  exact (Complex.continuous_ofReal.comp (continuous_finsetSum _
    (fun n _ => continuous_const.mul (perron_continuous_mxS n)))).continuousAt

end Formalism.PerronGeneral
