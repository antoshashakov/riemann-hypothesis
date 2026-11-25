module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GlobalTheory.CompanionTheory.Strip

theorem strip_open_real_discs (n : ℕ) (X : Fin n → ℝ) :
    IsOpen {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} ∧
    (∀ t : ℝ, (t : ℂ) ∈ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4}) ∧
    ∀ z ∈ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4}, ∃ (t ρ : ℝ), 0 < ρ ∧
      z ∈ Metric.ball (t : ℂ) ρ ∧
      Metric.ball (t : ℂ) ρ ⊆ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} := by
  set S := {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} with hS
  -- the admissible imaginary parts form an open subset of the real line
  have hV : IsOpen {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
  refine ⟨?_, ?_, ?_⟩
  · rw [hS, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
  · simp [hS, Real.pi_pos]
  · intro z hz
    obtain ⟨ε, hε, hball⟩ :=
      Metric.isOpen_iff.mp hV _ (by simpa only [hS, abs_mul, Set.mem_ofPred_eq] using hz)
    have hρ : ∀ j, (|z.im| + ε / 2) * |X j| < Real.pi / 4 :=
      hball (show |z.im| + ε / 2 ∈ Metric.ball |z.im| ε by
        rw [Real.ball_eq_Ioo]
        constructor <;> linarith)
    refine ⟨z.re, |z.im| + ε / 2, by positivity, ?_, ?_⟩
    · rw [Metric.mem_ball]
      simp [Complex.dist_eq, Complex.norm_def, Complex.normSq, Real.sqrt_mul_self_eq_abs, hε]
    · intro w hw j
      rw [Metric.mem_ball] at hw
      have him : |w.im| < |z.im| + ε / 2 := by
        have h := Complex.abs_im_le_norm (w - (z.re : ℂ))
        simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, dist_eq_norm] at h hw
        linarith
      calc |w.im * X j| = |w.im| * |X j| := abs_mul _ _
        _ ≤ (|z.im| + ε / 2) * |X j| := mul_le_mul_of_nonneg_right him.le (abs_nonneg _)
        _ < Real.pi / 4 := hρ j

end GlobalTheory.CompanionTheory.Strip
