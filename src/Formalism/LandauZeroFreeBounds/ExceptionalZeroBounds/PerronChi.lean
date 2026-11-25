module

public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
public import Formalism.DefsOC
public import Formalism.ZetaNonvanishing.MellinSAux
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Perron
import Formalism.ZetaNonvanishing.MellinSgen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.MellinInversion
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
public import Mathlib.NumberTheory.LSeries.Linearity
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

namespace Formalism.ZeroFreeDirichlet

section
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

def vonMangoldtCharRe (n : ℕ) : ℝ := (Λ n : ℝ) * (χ (n : ZMod q)).re

def vonMangoldtCharIm (n : ℕ) : ℝ := (Λ n : ℝ) * (χ (n : ZMod q)).im

lemma vonMangoldtCharRe_bound (n : ℕ) : |vonMangoldtCharRe χ n| ≤ 1 * Λ n := by
  unfold vonMangoldtCharRe
  have hΛ : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  rw [abs_mul, abs_of_nonneg hΛ, one_mul]
  refine mul_le_of_le_one_right hΛ ?_
  refine le_trans ?_ (DirichletCharacter.norm_le_one χ (n : ZMod q))
  first
  | exact Complex.abs_re_le_norm _
  | exact Complex.abs_re_le_abs _

lemma vonMangoldtCharIm_bound (n : ℕ) : |vonMangoldtCharIm χ n| ≤ 1 * Λ n := by
  unfold vonMangoldtCharIm
  have hΛ : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  rw [abs_mul, abs_of_nonneg hΛ, one_mul]
  refine mul_le_of_le_one_right hΛ ?_
  refine le_trans ?_ (DirichletCharacter.norm_le_one χ (n : ZMod q))
  first
  | exact Complex.abs_im_le_norm _
  | exact Complex.abs_im_le_abs _

lemma vonMangoldtCharRe_zero : vonMangoldtCharRe χ 0 = 0 := by simp [vonMangoldtCharRe]

lemma vonMangoldtCharIm_zero : vonMangoldtCharIm χ 0 = 0 := by simp [vonMangoldtCharIm]

lemma chebyshev_character_re_im (x : ℝ) :
    Schi χ x = (Formalism.Sa (vonMangoldtCharRe χ) x : ℂ) + I * (Formalism.Sa (vonMangoldtCharIm χ) x : ℂ) := by
  unfold Schi Formalism.Sa vonMangoldtCharRe vonMangoldtCharIm
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  conv_lhs => rw [← Complex.re_add_im (χ (n : ZMod q))]
  ring

lemma chebyshev_character_eq_zero_of_le_one {x : ℝ} (hx : x ≤ 1) : Schi χ x = 0 := by
  unfold Schi
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_Icc] at hn
  have h1 : ⌊x⌋₊ ≤ 1 := (Nat.floor_mono hx).trans_eq Nat.floor_one
  have hn1 : n = 1 := by omega
  subst hn1
  simp

end

section
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

lemma lseries_summable_of_vonMangoldt_bound {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1 * Λ n) {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (fun n => (a n : ℂ)) w := by
  refine Summable.of_norm_bounded (ArithmeticFunction.LSeriesSummable_vonMangoldt hw).norm fun n =>
    LSeries.norm_term_le _ ?_
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    one_mul] using ha n

lemma neg_log_deriv_eq_lseries_mul_vonMangoldt {w : ℂ} (hw : 1 < w.re) : negLD χ w = LSeries (↗χ * ↗Λ) w := by
  unfold negLD
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hw, neg_div]
  have hEq : ∀ s : ℂ, 1 < s.re → DirichletCharacter.LFunction χ s = L (fun n => χ n) s :=
    fun s hs => DirichletCharacter.LFunction_eq_LSeries χ hs
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 w] L (fun n => χ n) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with s hs
    exact hEq s hs
  rw [hev.deriv_eq, hEq w hw]

lemma neg_log_deriv_eq_lseries_re_im {w : ℂ} (hw : 1 < w.re) :
    negLD χ w = LSeries (fun n => (vonMangoldtCharRe χ n : ℂ)) w +
      I * LSeries (fun n => (vonMangoldtCharIm χ n : ℂ)) w := by
  have h1 := lseries_summable_of_vonMangoldt_bound (vonMangoldtCharRe_bound χ) hw
  have h2 := lseries_summable_of_vonMangoldt_bound (vonMangoldtCharIm_bound χ) hw
  rw [neg_log_deriv_eq_lseries_mul_vonMangoldt χ hw, ← LSeries_smul, ← LSeries_add h1 (h2.smul I)]
  congr 1
  ext n
  simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    vonMangoldtCharRe, vonMangoldtCharIm]
  push_cast
  conv_lhs => rw [← Complex.re_add_im (χ (n : ZMod q))]
  ring

lemma norm_neg_log_deriv_le_tsum {σ₀ : ℝ} (hσ : 1 < σ₀) (w : ℂ) (hw : w.re = σ₀) :
    ‖negLD χ w‖ ≤ ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := by
  rw [neg_log_deriv_eq_lseries_mul_vonMangoldt χ (by simpa [hw] using hσ)]
  refine PerronGeneral.norm_lseries_le_of_re_eq
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)) (by simpa using hw) fun n => ?_
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)

lemma perron_integrand_continuous {y : ℝ} (hy : 0 < y) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    Continuous (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + t * I)) := by
  refine (PerronGeneral.continuous_lseries_kernel
    (fun _ hw => DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hw) hy hσ).congr fun t => ?_
  unfold PerronGeneral.kernel
  simp (config := { singlePass := true }) only
    [← neg_log_deriv_eq_lseries_mul_vonMangoldt χ (by simp [hσ] : 1 < ((σ₀ : ℂ) + t * I).re)]
  rfl

lemma perron_integrand_integrable {y : ℝ} (hy : 0 < y) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    Integrable (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + t * I)) := by
  exact PerronGeneral.integrable_kernel (g := negLD χ) hy hσ
    (perron_integrand_continuous χ hy hσ)
    (fun t => norm_neg_log_deriv_le_tsum χ hσ ((σ₀ : ℂ) + t * I) (by simp))
    (Formalism.ZF.perron_denom_bound hσ)

end

section
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

lemma summatory_eq_sum_range {a : ℕ → ℝ} (ha0 : a 0 = 0) {N : ℕ} {x : ℝ} (hx : x < N) :
    Formalism.Sa a x = ∑ n ∈ Finset.range N, a n * Formalism.mxS n x := by
  exact PerronGeneral.summatory_eq_sum_range ha0 hx

lemma summatory_function_continuousAt {a : ℕ → ℝ} (ha0 : a 0 = 0) (y : ℝ) :
    ContinuousAt (fun x => (Formalism.Sa a x : ℂ)) y := by
  exact PerronGeneral.summatory_function_continuousAt ha0 y

lemma chebyshev_character_continuousAt (y : ℝ) : ContinuousAt (fun x => Schi χ x) y := by
  have h : (fun x => Schi χ x) =
      fun x => (Formalism.Sa (vonMangoldtCharRe χ) x : ℂ) + I * (Formalism.Sa (vonMangoldtCharIm χ) x : ℂ) :=
    funext (chebyshev_character_re_im χ)
  rw [h]
  exact (summatory_function_continuousAt (vonMangoldtCharRe_zero χ) y).add
    (continuousAt_const.mul (summatory_function_continuousAt (vonMangoldtCharIm_zero χ) y))

lemma summatory_rpow_integrableOn {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1 * Λ n) {w : ℂ} (hw : 1 < w.re) :
    IntegrableOn (fun x : ℝ => (Formalism.Sa a x : ℂ) * (x : ℂ) ^ (-w - 1)) (Ioi 1) := by
  obtain ⟨hm, hI, -⟩ := Formalism.mellinSgen a 1 ha
  refine Integrable.mono' (hI w.re hw) ?_ ?_
  · exact ((Complex.measurable_ofReal.comp hm).mul
      (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs]
    simp

lemma chebyshev_character_integrableOn {w : ℂ} (hw : 1 < w.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-w - 1) • Schi χ x) (Ioi 1) := by
  refine ((summatory_rpow_integrableOn (vonMangoldtCharRe_bound χ) hw).add
    ((summatory_rpow_integrableOn (vonMangoldtCharIm_bound χ) hw).const_mul I)).congr_fun (fun x _ => ?_) measurableSet_Ioi
  rw [Pi.add_apply, chebyshev_character_re_im χ x, smul_eq_mul]
  ring

lemma mellin_chebyshev_character {w : ℂ} (hw : 1 < w.re) :
    mellin (fun x : ℝ => Schi χ x) (-w) = negLD χ w / (w * (w - 1)) := by
  have h1 := (Formalism.mellinSgen _ 1 (vonMangoldtCharRe_bound χ)).2.2 w hw
  have h2 := (Formalism.mellinSgen _ 1 (vonMangoldtCharIm_bound χ)).2.2 w hw
  unfold mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi zero_le_one) ?_]
  · calc ∫ t in Ioi (1:ℝ), (t : ℂ) ^ (-w - 1) • Schi χ t
        = ∫ t in Ioi (1:ℝ), ((Formalism.Sa (vonMangoldtCharRe χ) t : ℂ) * (t : ℂ) ^ (-w - 1) +
            I * ((Formalism.Sa (vonMangoldtCharIm χ) t : ℂ) * (t : ℂ) ^ (-w - 1))) := by
          congr 1; funext t; rw [chebyshev_character_re_im χ t, smul_eq_mul]; ring
      _ = (∫ t in Ioi (1:ℝ), (Formalism.Sa (vonMangoldtCharRe χ) t : ℂ) * (t : ℂ) ^ (-w - 1)) +
            I * ∫ t in Ioi (1:ℝ), (Formalism.Sa (vonMangoldtCharIm χ) t : ℂ) * (t : ℂ) ^ (-w - 1) := by
          rw [integral_add (summatory_rpow_integrableOn (vonMangoldtCharRe_bound χ) hw)
            ((summatory_rpow_integrableOn (vonMangoldtCharIm_bound χ) hw).const_mul I), integral_const_mul]
      _ = _ := by
          rw [h1, h2, neg_log_deriv_eq_lseries_re_im χ hw]
          ring
  · intro x hx
    have hx1 : x ≤ 1 := not_lt.mp hx.2
    simp [chebyshev_character_eq_zero_of_le_one χ hx1]

lemma mellin_convergent_chebyshev_character {σ₀ : ℝ} (hσ : 1 < σ₀) :
    MellinConvergent (fun x : ℝ => Schi χ x) ((-σ₀ : ℝ) : ℂ) := by
  exact PerronGeneral.mellin_convergent_of_support
    (fun _ hx => chebyshev_character_eq_zero_of_le_one χ hx)
    (chebyshev_character_integrableOn χ (w := (σ₀ : ℂ)) (by simpa using hσ))

lemma perron_vertical_integrable {σ₀ : ℝ} (hσ : 1 < σ₀) :
    VerticalIntegrable (mellin (fun x : ℝ => Schi χ x)) (-σ₀) := by
  exact PerronGeneral.vertical_integrable hσ (fun _ hw => mellin_chebyshev_character χ hw)
    (perron_integrand_integrable χ one_pos hσ)

end

theorem perron_formula_character : PerronChi := by
  intro q _ χ y hy σ₀ hσ
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  exact ⟨perron_integrand_integrable χ hy0 hσ, PerronGeneral.mellin_inversion hy0 hσ
    (fun _ hw => mellin_chebyshev_character χ hw) (mellin_convergent_chebyshev_character χ hσ)
    (perron_vertical_integrable χ hσ) (chebyshev_character_continuousAt χ y)⟩

end Formalism.ZeroFreeDirichlet
