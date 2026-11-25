module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.DefsOC
public import Formalism.ZetaNonvanishing.MellinSAux
public import Formalism.ZetaNonvanishing.MellinSgen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.PerronGeneral

@[expose] public section

open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation

noncomputable section

namespace Formalism.ZF

lemma perron_Sz_eq_Sa : Formalism.Sz = Formalism.Sa (fun n => (Λ n : ℝ)) := rfl

lemma perron_Sz_eq_zero_of_le_one {x : ℝ} (hx : x ≤ 1) : Formalism.Sz x = 0 := by
  unfold Formalism.Sz
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hx0 : 0 ≤ x := by
    by_contra h
    push_neg at h
    have h1 := Nat.floor_of_nonpos h.le
    omega
  have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0).1 hn.2
  have hn1 : n = 1 := by
    have h1 : (n : ℝ) ≤ 1 := hnx.trans hx
    have h2 : n ≤ 1 := by exact_mod_cast h1
    omega
  subst hn1
  simp [ArithmeticFunction.vonMangoldt_apply_one]

lemma perron_continuous_mxS (n : ℕ) : Continuous (Formalism.mxS n) := by
  exact PerronGeneral.perron_continuous_mxS n

lemma perron_Sz_continuousAt (y : ℝ) : ContinuousAt (fun x => (Formalism.Sz x : ℂ)) y := by
  simpa only [perron_Sz_eq_Sa] using
    PerronGeneral.summatory_function_continuousAt (a := fun n => (Λ n : ℝ)) (by simp) y

lemma perron_norm_LSeries_le {σ₀ : ℝ} (hσ : 1 < σ₀) (w : ℂ) (hw : w.re = σ₀) :
    ‖LSeries ↗Λ w‖ ≤ ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := by
  exact PerronGeneral.norm_lseries_le_of_re_eq
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)) (by simpa using hw) (fun _ => le_rfl)

lemma perron_denom_bound {σ₀ : ℝ} (hσ : 1 < σ₀) (t : ℝ) :
    min ((σ₀ - 1) ^ 2) 1 * (1 + t ^ 2) ≤ ‖((σ₀ : ℂ) + t * I) * ((σ₀ : ℂ) + t * I - 1)‖ := by
  set m := min ((σ₀ - 1) ^ 2) 1 with hm
  have hm0 : 0 ≤ m := le_min (sq_nonneg _) zero_le_one
  have hm1 : m ≤ 1 := min_le_right _ _
  have hm2 : m ≤ (σ₀ - 1) ^ 2 := min_le_left _ _
  have hn1 : ‖((σ₀ : ℂ) + t * I)‖ ^ 2 = σ₀ ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hn2 : ‖((σ₀ : ℂ) + t * I - 1)‖ ^ 2 = (σ₀ - 1) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have a0 : 0 ≤ m * (1 + t ^ 2) := by positivity
  have a1 : m * (1 + t ^ 2) ≤ σ₀ ^ 2 + t ^ 2 := by nlinarith
  have a2 : m * (1 + t ^ 2) ≤ (σ₀ - 1) ^ 2 + t ^ 2 := by nlinarith
  have key : (m * (1 + t ^ 2)) ^ 2 ≤ (σ₀ ^ 2 + t ^ 2) * ((σ₀ - 1) ^ 2 + t ^ 2) := by
    rw [sq]
    exact mul_le_mul a1 a2 a0 (by positivity)
  have e : (‖((σ₀ : ℂ) + t * I)‖ * ‖((σ₀ : ℂ) + t * I - 1)‖) ^ 2 =
      (σ₀ ^ 2 + t ^ 2) * ((σ₀ - 1) ^ 2 + t ^ 2) := by
    rw [mul_pow, hn1, hn2]
  rw [norm_mul]
  exact (pow_le_pow_iff_left₀ a0 (by positivity) two_ne_zero).1 (key.trans e.symm.le)

lemma perron_Fy_eq_LSeries (y : ℝ) (w : ℂ) (hw : 1 < w.re) :
    Fy y w = LSeries ↗Λ w * (y : ℂ) ^ w / (w * (w - 1)) := by
  unfold Fy
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw]
  ring

lemma perron_continuous_Fy {y : ℝ} (hy : 0 < y) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    Continuous (fun t : ℝ => Fy y ((σ₀ : ℂ) + t * I)) := by
  refine (PerronGeneral.continuous_lseries_kernel
    (fun _ hw => ArithmeticFunction.LSeriesSummable_vonMangoldt hw) hy hσ).congr fun t => ?_
  exact (perron_Fy_eq_LSeries y _ (by simp [hσ])).symm

lemma perron_integrable_Fy {y : ℝ} (hy : 0 < y) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    Integrable (fun t : ℝ => Fy y ((σ₀ : ℂ) + t * I)) := by
  refine PerronGeneral.integrable_kernel (g := fun w => -(deriv riemannZeta w / riemannZeta w))
    (B := ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖) hy hσ (perron_continuous_Fy hy hσ) ?_
    (perron_denom_bound hσ)
  intro t
  have h := perron_norm_LSeries_le hσ ((σ₀ : ℂ) + t * I) (by simp)
  rwa [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simp [hσ]), neg_div] at h

lemma perron_mellinSgen_Λ :
    Measurable (Formalism.Sa (fun n => (Λ n : ℝ))) ∧
    (∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => |Formalism.Sa (fun n => (Λ n : ℝ)) x| * x ^ (-σ - 1))
      (Ioi 1)) ∧
    ∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1:ℝ), (Formalism.Sa (fun n => (Λ n : ℝ)) x : ℂ) * (x : ℂ) ^ (-s - 1) =
        LSeries (fun n => ((Λ n : ℝ) : ℂ)) s / (s * (s - 1)) := Formalism.mellinSgen (fun n => (Λ n : ℝ)) 1 (fun n => by
    rw [one_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg])

lemma perron_mellin_Sz {w : ℂ} (hw : 1 < w.re) :
    mellin (fun x : ℝ => (Formalism.Sz x : ℂ)) (-w) =
      -(deriv riemannZeta w / riemannZeta w) / (w * (w - 1)) := by
  have h1 := perron_mellinSgen_Λ.2.2 w hw
  rw [← perron_Sz_eq_Sa] at h1
  rw [mellin]
  have hzero : ∀ t ∈ Ioi (0:ℝ) \ Ioi 1, (t : ℂ) ^ (-w - 1) • ((Formalism.Sz t : ℝ) : ℂ) = 0 := by
    intro t ht
    have : t ≤ 1 := not_lt.1 ht.2
    rw [perron_Sz_eq_zero_of_le_one this]
    simp
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi zero_le_one) hzero]
  simp_rw [smul_eq_mul, mul_comm ((_ : ℂ) ^ (-w - 1))]
  rw [h1, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw]
  ring

lemma perron_mellinConvergent {σ₀ : ℝ} (hσ : 1 < σ₀) :
    MellinConvergent (fun x : ℝ => (Formalism.Sz x : ℂ)) ((-σ₀ : ℝ) : ℂ) := by
  refine PerronGeneral.mellin_convergent_of_support
    (fun _ hx => by simp [perron_Sz_eq_zero_of_le_one hx]) ?_
  have h2 := perron_mellinSgen_Λ.2.1 σ₀ hσ
  rw [← perron_Sz_eq_Sa] at h2
  have hmeas : Measurable Formalism.Sz := by
    rw [perron_Sz_eq_Sa]; exact perron_mellinSgen_Λ.1
  have hI1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (((-σ₀ : ℝ) : ℂ) - 1) • ((Formalism.Sz t : ℝ) : ℂ)) (Ioi 1) := by
    refine Integrable.mono' h2 ?_ ?_
    · exact ((Complex.continuous_ofReal.measurable.pow_const _).smul
        (Complex.continuous_ofReal.measurable.comp hmeas)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht), Complex.norm_real,
        Real.norm_eq_abs]
      simp [mul_comm]
  simpa only [Complex.ofReal_neg] using hI1

lemma perron_verticalIntegrable {σ₀ : ℝ} (hσ : 1 < σ₀) :
    VerticalIntegrable (mellin (fun x : ℝ => (Formalism.Sz x : ℂ))) (-σ₀) := by
  exact PerronGeneral.vertical_integrable hσ (fun _ hw => perron_mellin_Sz hw)
    (perron_integrable_Fy one_pos hσ)

theorem perron_formula : Perron := by
  intro y hy σ₀ hσ
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  exact ⟨perron_integrable_Fy hy0 hσ, PerronGeneral.mellin_inversion hy0 hσ
    (fun _ hw => perron_mellin_Sz hw) (perron_mellinConvergent hσ)
    (perron_verticalIntegrable hσ) (perron_Sz_continuousAt y)⟩

end Formalism.ZF
