module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LandauLocalOf
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivBound
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZeroFactor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.AbsMax
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

import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LocalZeroFactorizationBounds

@[expose] public section

open Complex Filter Topology Metric

noncomputable section

namespace Formalism.ZeroFreeDirichlet

private theorem differentiable_prod_sub_pow (Z : Finset ℂ) (m : ℂ → ℕ) :
    Differentiable ℂ (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) := by
  refine Finset.induction_on Z ?_ ?_
  · simp
  · intro a s ha ih
    simp only [Finset.prod_insert ha]
    exact ((differentiable_id.sub_const a).pow (m a)).mul ih

private theorem deriv_sub_mul_at_self {g : ℂ → ℂ} {ρ : ℂ} (hg : DifferentiableAt ℂ g ρ) :
    deriv (fun z => (z - ρ) * g z) ρ = g ρ := by
  have h : HasDerivAt (fun z => (z - ρ) * g z) (1 * g ρ + (ρ - ρ) * deriv g ρ) ρ :=
    ((hasDerivAt_id ρ).sub_const ρ).mul hg.hasDerivAt
  rw [h.deriv]
  ring

private theorem deriv_eq_zero_iff_mult_of_local_factor {f k : ℂ → ℂ} {ρ : ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hk : DifferentiableAt ℂ k ρ) (hk0 : k ρ ≠ 0)
    (hf : f =ᶠ[𝓝 ρ] fun w => (w - ρ) ^ n * k w) :
    (deriv f ρ = 0 → 2 ≤ n) ∧ (deriv f ρ ≠ 0 → n = 1) := by
  rw [hf.deriv_eq]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hfun : (fun w => (w - ρ) ^ (j + 1) * k w) = fun w => (w - ρ) * ((w - ρ) ^ j * k w) := by
    funext w
    ring
  have hg : DifferentiableAt ℂ (fun w => (w - ρ) ^ j * k w) ρ := by
    fun_prop
  rw [hfun, deriv_sub_mul_at_self hg]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp only [pow_zero, one_mul]
    exact ⟨fun h => absurd h hk0, fun _ => by simp⟩
  · have h0 : (ρ - ρ) ^ j = 0 := by
      rw [sub_self]
      exact zero_pow hj.ne'
    rw [h0, zero_mul]
    exact ⟨fun _ => by omega, fun h => absurd rfl h⟩

theorem exists_localZeroExpansion_of_bound (f : ℂ → ℂ) (z₀ : ℂ) (r M : ℝ) (hr : 0 < r) (hM : 1 ≤ M)
    (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ r)) (hfz₀ : f z₀ ≠ 0)
    (hbound : ∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ = 0 → 2 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ ≠ 0 → m ρ = 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log M / r := by
  have hr3 : 0 < r / 3 := by linarith
  obtain ⟨Z, m, h, hZ, hm, hhd, hh0, hfac⟩ :=
    Formalism.ZF.zeroFactorization f z₀ r (r / 3) hr3 (by linarith) hf hfz₀
  have hsub : ∀ z ∈ closedBall z₀ (r / 3), z ∈ ball z₀ r := fun z hz => by
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  have hloc : ∀ z ∈ ball z₀ r, f =ᶠ[𝓝 z] fun w => (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * h w := by
    intro z hz
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hfac w (ball_subset_closedBall hw)
  have hhdiff : ∀ z ∈ ball z₀ r, DifferentiableAt ℂ h z := fun z hz =>
    hhd.differentiableAt (Filter.mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall)
  have hZb : ∀ ρ ∈ Z, ρ ∈ closedBall z₀ (r / 3) := fun ρ hρ => ((hZ ρ).1 hρ).1
  have horder : ∀ ρ ∈ Z, (deriv f ρ = 0 → 2 ≤ m ρ) ∧ (deriv f ρ ≠ 0 → m ρ = 1) := by
    intro ρ hρ
    have hρb := hsub ρ (hZb ρ hρ)
    refine deriv_eq_zero_iff_mult_of_local_factor (k := fun w => (∏ ρ' ∈ Z.erase ρ, (w - ρ') ^ m ρ') * h w)
      (hm ρ hρ) ((differentiable_prod_sub_pow (Z.erase ρ) m ρ).mul (hhdiff ρ hρb)) ?_ ?_
    · exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ' hρ' =>
        pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hρ').symm)) (hh0 ρ (hZb ρ hρ))
    · filter_upwards [hloc ρ hρb] with w hw
      rw [hw, ← mul_assoc, Finset.mul_prod_erase Z (fun ρ' => (w - ρ') ^ m ρ') hρ]
  obtain ⟨hcount, hrem⟩ := Formalism.ZF.LocalZeroFactorizationBounds.bounds_of_factorization
    Formalism.ZF.logDerivBoundOnBall hr hM Z m (fun ρ hρ => (hZ ρ).mp hρ) hhd hh0 hfac hbound
  exact ⟨Z, m, hZ, hm, fun ρ hρ => (horder ρ hρ).1, fun ρ hρ => (horder ρ hρ).2, hcount, hrem⟩

end Formalism.ZeroFreeDirichlet
