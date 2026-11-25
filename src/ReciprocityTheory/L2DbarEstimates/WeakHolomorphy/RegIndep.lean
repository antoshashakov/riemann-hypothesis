module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.IntegralMollProfBall
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegConv
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Convolution

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem mollify_mollify_swap {n : ℕ} {u : V n → ℂ} (hu : Integrable u) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) (x : V n) :
    ∫ w, (moll n s (x - w) : ℂ) * ∫ y, (moll n t (w - y) : ℂ) * u y =
      ∫ y, ((∫ w, moll n s (x - w) * moll n t (w - y) : ℝ) : ℂ) * u y := by
  obtain ⟨C, hC⟩ := (moll_contDiff n s).continuous.bounded_above_of_compact_support
    (moll_hasCompactSupport n hs)
  have hg : Integrable (fun v : V n => (moll n t v : ℂ)) := (moll_integrable n ht).ofReal
  have hI := hu.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hg
  have hc : Continuous (fun p : V n × V n => (moll n s (x - p.1) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((moll_contDiff n s).continuous.comp (continuous_const.sub continuous_fst))
  set F : V n × V n → ℂ := fun p => (moll n s (x - p.1) : ℂ) *
    (ContinuousLinearMap.mul ℂ ℂ) (u p.2) ((fun v : V n => (moll n t v : ℂ)) (p.1 - p.2)) with hFdef
  have hF : Integrable F (volume.prod volume) := by
    refine (hI.norm.const_mul C).mono' (hc.aestronglyMeasurable.mul hI.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    rw [hFdef, norm_mul]
    gcongr
    have h1 := hC (x - p.1)
    simpa using h1
  calc ∫ w, (moll n s (x - w) : ℂ) * ∫ y, (moll n t (w - y) : ℂ) * u y
      = ∫ w, ∫ y, F (w, y) := by
        congr 1; funext w
        rw [← integral_const_mul]
        congr 1; funext y
        simp only [hFdef, ContinuousLinearMap.mul_apply']
        ring
    _ = ∫ y, ∫ w, F (w, y) := integral_integral_swap hF
    _ = ∫ y, ((∫ w, moll n s (x - w) * moll n t (w - y) : ℝ) : ℂ) * u y := by
        congr 1; funext y
        rw [← integral_complex_ofReal, ← integral_mul_const]
        congr 1; funext w
        simp only [hFdef, ContinuousLinearMap.mul_apply', Complex.ofReal_mul]
        ring

theorem moll_conv_symm (n : ℕ) (s t : ℝ) (x y : V n) :
    ∫ w, moll n s (x - w) * moll n t (w - y) = ∫ w, moll n t (x - w) * moll n s (w - y) := by
  calc ∫ w, moll n s (x - w) * moll n t (w - y)
      = ∫ w, moll n s (x - (x + y - w)) * moll n t ((x + y - w) - y) :=
        (integral_sub_left_eq_self (fun w => moll n s (x - w) * moll n t (w - y)) volume
          (x + y)).symm
    _ = ∫ w, moll n t (x - w) * moll n s (w - y) := by
        congr 1; funext w
        rw [mul_comm]
        congr 2 <;> abel

theorem mollify_indep {n : ℕ} {Ω : Set (V n)} {u : V n → ℂ} {s t : ℝ} {x : V n}
    (hΩ : IsOpen Ω) (hu : Integrable u) (hw : WeakHolo Ω u) (hs : 0 < s) (ht : 0 < t)
    (hx : closedBall x (s + t) ⊆ Ω) :
    mollify n s u x = mollify n t u x := by
  have hA : DifferentiableOn ℂ (mollify n t u) (ball x s) := by
    intro w hwb
    rw [Metric.mem_ball] at hwb
    refine (mollify_differentiableAt hΩ hu hw ht ((Metric.closedBall_subset_closedBall' ?_).trans hx)).differentiableWithinAt
    linarith
  have hB : DifferentiableOn ℂ (mollify n s u) (ball x t) := by
    intro w hwb
    rw [Metric.mem_ball] at hwb
    refine (mollify_differentiableAt hΩ hu hw hs ((Metric.closedBall_subset_closedBall' ?_).trans hx)).differentiableWithinAt
    linarith
  calc mollify n s u x = ∫ w, (moll n t (x - w) : ℂ) * mollify n s u w := (moll_mean ht hB).symm
    _ = ∫ y, ((∫ w, moll n t (x - w) * moll n s (w - y) : ℝ) : ℂ) * u y :=
        mollify_mollify_swap hu ht hs x
    _ = ∫ y, ((∫ w, moll n s (x - w) * moll n t (w - y) : ℝ) : ℂ) * u y := by
        congr 1; funext y; rw [moll_conv_symm n t s x y]
    _ = ∫ w, (moll n s (x - w) : ℂ) * mollify n t u w := (mollify_mollify_swap hu hs ht x).symm
    _ = mollify n t u x := moll_mean hs hA

end ReciprocityTheory.L2DbarEstimates.C
