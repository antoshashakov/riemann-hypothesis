module

public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.DzDifferentiableOn
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeriesComplex
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

namespace ComplexPowerDifferenceIntegral

lemma partial_dz (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, dz s i =
      1 - (((N : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s) -
        (s - 1) * ∑ i ∈ Finset.range N, ((((i : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s) := by
  simp only [dz, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  simpa [Finset.sum_sub_distrib, Nat.cast_add] using
    Finset.sum_range_sub' (fun n : ℕ => (((n : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s)) N

lemma one_lt_identity {s : ℂ} (hs : 1 < s.re) : (s - 1) * riemannZeta s = s - Dz s := by
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
    simpa only [zeta_eq_tsum_one_div_nat_add_one_cpow hs, Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)).hasSum
  have hG : HasSum (fun i : ℕ => ((((i : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s)) (riemannZeta s - 1) := by
    simpa [Nat.cast_add, cpow_neg, one_div] using (hasSum_nat_add_iff' 1).mpr hz
  have hc : Tendsto (fun n : ℕ => (((n : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    refine ((tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp hn).congr (fun n => ?_)
    rw [Function.comp_apply, norm_cpow_eq_rpow_re_of_pos (by positivity), sub_re, one_re, neg_sub]
  have hD := (summable_norm_dz (lt_trans zero_lt_one hs)).of_norm.hasSum.tendsto_sum_nat
  simp_rw [partial_dz] at hD
  have h : Dz s = 1 - 0 - (s - 1) * (riemannZeta s - 1) := tendsto_nhds_unique hD
    ((tendsto_const_nhds.sub hc).sub (hG.tendsto_sum_nat.const_mul (s - 1)))
  linear_combination h

lemma riemannZetaOne_eq_one_sub_of_re_pos {s : ℂ} (hs : 0 < s.re) : riemannZeta₁ s = s - Dz s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hU)
    ((differentiableOn_id.sub Dz_differentiableOn).analyticOnNhd hU)
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := (2 : ℂ)) (by norm_num) ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num)] with z hz
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  change riemannZeta₁ z = z - Dz z
  rw [← one_lt_identity hz, riemannZeta_eq_inv_sub_mul hz1, mul_inv_cancel_left₀ (sub_ne_zero.mpr hz1)]

end ComplexPowerDifferenceIntegral

end Formalism.ZF
