module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.LFunctionEqGOfOneLt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Formalism.LFunctionBounds.AbelSummation

@[expose] public section

open Complex Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums

open Formalism.FX.LFunctionPartialSum

variable (f : ℕ → ℂ)

def Ap (n : ℕ) : ℂ := ∑ k ∈ Finset.Icc 1 n, f k

def dterm (s : ℂ) (n : ℕ) : ℂ := Ap f n * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s))

def G (s : ℂ) : ℂ := ∑' n, dterm f s n

lemma Ap_zero : Ap f 0 = 0 := by
  unfold Ap
  exact Finset.sum_eq_zero (fun i hi => by rw [Finset.mem_Icc] at hi; omega)

lemma Ap_succ (n : ℕ) : Ap f (n + 1) = Ap f n + f (n + 1) := by
  unfold Ap
  exact Finset.sum_Icc_succ_top (by omega) f

lemma dterm_zero (s : ℂ) : dterm f s 0 = 0 := by
  rw [dterm, Ap_zero, zero_mul]

private lemma natCast_cpow_neg_sub_succ_eq_mul_integral (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s) = s * ∫ t in (n : ℝ)..((n : ℝ) + 1), (t : ℂ) ^ (-s - 1) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  simpa using cpow_sub_eq_integral (Nat.cast_pos.mpr (by omega) : (0 : ℝ) < n) hs0

private lemma norm_cpow_neg_sub_succ_le_norm_mul_rpow (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
  simpa using norm_cpow_sub_le' (Nat.cast_pos.mpr (by omega) : (0 : ℝ) < n) hs

lemma norm_dterm_le {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖dterm f s n‖ ≤ B * (‖s‖ * (n : ℝ) ^ (-s.re - 1)) := by
  exact Formalism.LFunctionBounds.AbelSummation.norm_dterm_le f hB hs n

private lemma norm_cpow_neg_sub_succ_le_telescoping (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)‖ ≤
      ‖s‖ / s.re * ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re)) := by
  simpa using norm_cpow_sub_le (Nat.cast_pos.mpr (by omega) : (0 : ℝ) < n) hs

lemma norm_dterm_le' {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖dterm f s n‖ ≤ B * (‖s‖ / s.re * ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re))) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  rw [dterm, norm_mul]
  exact mul_le_mul (hB n) (norm_cpow_neg_sub_succ_le_telescoping s hs n hn) (norm_nonneg _) hB0

lemma summable_norm_dterm {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n => ‖dterm f s n‖) := by
  exact Formalism.LFunctionBounds.AbelSummation.summable_norm_dterm f hB hs

lemma summable_dterm {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Summable (dterm f s) := (summable_norm_dterm f hB hs).of_norm

lemma partial_identity (s : ℂ) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), dterm f s n + Ap f M * ((M : ℂ) + 1) ^ (-s) =
      ∑ n ∈ Finset.Icc 1 M, f n * (n : ℂ) ^ (-s) := by
  exact Formalism.LFunctionBounds.AbelSummation.partial_identity f s M

lemma G_differentiableOn {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) :
    DifferentiableOn ℂ (G f) {s : ℂ | 0 < s.re} := by
  exact Formalism.LFunctionBounds.AbelSummation.G_differentiableOn f hB

private lemma norm_Ap_mul_succ_cpow_neg_le {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) (s : ℂ) (M : ℕ) :
    ‖Ap f M * ((M : ℂ) + 1) ^ (-s)‖ ≤ B * ((M : ℝ) + 1) ^ (-s.re) := by
  have e : ((M : ℂ) + 1) = (((M : ℝ) + 1 : ℝ) : ℂ) := by simp
  rw [norm_mul, e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp only [Complex.neg_re]
  exact mul_le_mul_of_nonneg_right (hB M) (Real.rpow_nonneg (by positivity) _)

lemma partial_tendsto_G {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, f n * (n : ℂ) ^ (-s)) atTop (𝓝 (G f s)) := by
  exact Formalism.LFunctionBounds.AbelSummation.partial_tendsto_G f hB hs

private lemma sum_range_rpow_neg_telescope (σ : ℝ) (N M : ℕ) :
    ∑ i ∈ Finset.range M, ((((i + (N + 1) : ℕ) : ℝ)) ^ (-σ) - ((((i + (N + 1) : ℕ) : ℝ)) + 1) ^ (-σ)) =
      ((N : ℝ) + 1) ^ (-σ) - (((M + N + 1 : ℕ) : ℝ)) ^ (-σ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring_nf

lemma norm_tail_le {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖∑' i, dterm f s (i + (N + 1))‖ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hc : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have hsum : Summable (fun i => dterm f s (i + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).2 (summable_dterm f hB hs)
  refine le_of_tendsto' (hsum.hasSum.tendsto_sum_nat.norm) (fun M => ?_)
  calc ‖∑ i ∈ Finset.range M, dterm f s (i + (N + 1))‖
        ≤ ∑ i ∈ Finset.range M, ‖dterm f s (i + (N + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range M, B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
          ((((i + (N + 1) : ℕ) : ℝ)) + 1) ^ (-s.re))) :=
        Finset.sum_le_sum fun i _ => norm_dterm_le' f hB hs (by omega)
    _ = B * (‖s‖ / s.re) * (((N : ℝ) + 1) ^ (-s.re) - (((M + N + 1 : ℕ) : ℝ)) ^ (-s.re)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, sum_range_rpow_neg_telescope]
        ring
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
        have h5 : 0 ≤ (((M + N + 1 : ℕ) : ℝ)) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have h6 : 0 ≤ B * (‖s‖ / s.re) := mul_nonneg hB0 hc
        nlinarith

lemma norm_G_sub_partial_le {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖G f s - ∑ n ∈ Finset.Icc 1 N, f n * (n : ℂ) ^ (-s)‖ ≤
      B * (1 + ‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
  rw [← partial_identity f s N]
  have hsum := summable_dterm f hB hs
  have hG : G f s = ∑ n ∈ Finset.range (N + 1), dterm f s n + ∑' i, dterm f s (i + (N + 1)) :=
    (hsum.sum_add_tsum_nat_add (N + 1)).symm
  rw [hG]
  have e : ∑ n ∈ Finset.range (N + 1), dterm f s n + ∑' i, dterm f s (i + (N + 1)) -
      (∑ n ∈ Finset.range (N + 1), dterm f s n + Ap f N * ((N : ℂ) + 1) ^ (-s)) =
      ∑' i, dterm f s (i + (N + 1)) - Ap f N * ((N : ℂ) + 1) ^ (-s) := by ring
  rw [e]
  have h1 := norm_tail_le f hB hs N
  have h2 : ‖Ap f N * ((N : ℂ) + 1) ^ (-s)‖ ≤ B * ((N : ℝ) + 1) ^ (-s.re) := by
    rw [norm_mul, natCast_add_one_eq, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hB N) (Real.rpow_nonneg (by positivity) _)
  calc ‖∑' i, dterm f s (i + (N + 1)) - Ap f N * ((N : ℂ) + 1) ^ (-s)‖
      ≤ ‖∑' i, dterm f s (i + (N + 1))‖ + ‖Ap f N * ((N : ℂ) + 1) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) + B * ((N : ℝ) + 1) ^ (-s.re) := add_le_add h1 h2
    _ = B * (1 + ‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
