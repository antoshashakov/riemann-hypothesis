module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.LFunctionBounds.ExpSumLowerBound
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.RectResidue
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

import
  Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.RectIntEqZeroOfDifferentiableOn

@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZF

theorem rdp_rectInt_eq_fx (g : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) :
    rectInt g x0 x1 y0 y1 = Formalism.FX.rectInt g x0 x1 y0 y1 := rfl

theorem rdp_rectInt_add (f1 f2 : ℂ → ℂ) (x0 x1 y0 y1 : ℝ)
    (hB1 : IntervalIntegrable (fun x : ℝ => f1 (x + y0 * I)) MeasureTheory.volume x0 x1)
    (hB2 : IntervalIntegrable (fun x : ℝ => f2 (x + y0 * I)) MeasureTheory.volume x0 x1)
    (hT1 : IntervalIntegrable (fun x : ℝ => f1 (x + y1 * I)) MeasureTheory.volume x0 x1)
    (hT2 : IntervalIntegrable (fun x : ℝ => f2 (x + y1 * I)) MeasureTheory.volume x0 x1)
    (hR1 : IntervalIntegrable (fun y : ℝ => f1 (x1 + y * I)) MeasureTheory.volume y0 y1)
    (hR2 : IntervalIntegrable (fun y : ℝ => f2 (x1 + y * I)) MeasureTheory.volume y0 y1)
    (hL1 : IntervalIntegrable (fun y : ℝ => f1 (x0 + y * I)) MeasureTheory.volume y0 y1)
    (hL2 : IntervalIntegrable (fun y : ℝ => f2 (x0 + y * I)) MeasureTheory.volume y0 y1) :
    rectInt (fun w => f1 w + f2 w) x0 x1 y0 y1 =
      rectInt f1 x0 x1 y0 y1 + rectInt f2 x0 x1 y0 y1 := by
  simp only [rectInt]
  rw [intervalIntegral.integral_add hB1 hB2, intervalIntegral.integral_add hT1 hT2,
    intervalIntegral.integral_add hR1 hR2, intervalIntegral.integral_add hL1 hL2]
  ring

theorem rdp_hasDerivAt_prim (a p w : ℂ) (hw : w ≠ p) :
    HasDerivAt (fun z => -a * (z - p)⁻¹) (a / (w - p) ^ 2) w := by
  have hwp : w - p ≠ 0 := sub_ne_zero.2 hw
  have h := (((hasDerivAt_id' w).sub_const p).inv hwp).const_mul (-a)
  convert h using 1
  all_goals first | rfl | ring | (field_simp; ring) | (simp; ring)

theorem rdp_horiz (a p : ℂ) (y x0 x1 : ℝ) (hy : y ≠ p.im) :
    ∫ x in x0..x1, a / ((x : ℂ) + y * I - p) ^ 2 =
      (-a * ((x1 : ℂ) + y * I - p)⁻¹) - (-a * ((x0 : ℂ) + y * I - p)⁻¹) := by
  have hne (x : ℝ) : (x : ℂ) + y * I ≠ p := fun h => hy (by simpa using congrArg Complex.im h)
  exact PI.EF.Rect.hint_of_hasDerivAt (f := fun s => a / (s - p) ^ 2)
    (fun x _ => rdp_hasDerivAt_prim a p _ (hne x))
    (fun x _ => continuousAt_const.div (by fun_prop) (pow_ne_zero 2 (sub_ne_zero.mpr (hne x))))

theorem rdp_vert (a p : ℂ) (x y0 y1 : ℝ) (hx : x ≠ p.re) :
    I * ∫ y in y0..y1, a / ((x : ℂ) + y * I - p) ^ 2 =
      (-a * ((x : ℂ) + y1 * I - p)⁻¹) - (-a * ((x : ℂ) + y0 * I - p)⁻¹) := by
  have hne (y : ℝ) : (x : ℂ) + y * I ≠ p := fun h => hx (by simpa using congrArg Complex.re h)
  exact PI.EF.Rect.vint_of_hasDerivAt (f := fun s => a / (s - p) ^ 2)
    (fun y _ => rdp_hasDerivAt_prim a p _ (hne y))
    (fun y _ => continuousAt_const.div (by fun_prop) (pow_ne_zero 2 (sub_ne_zero.mpr (hne y))))

theorem rdp_rectInt_double (a p : ℂ) (x0 x1 y0 y1 : ℝ) (h1 : x0 < p.re) (h2 : p.re < x1)
    (h3 : y0 < p.im) (h4 : p.im < y1) :
    rectInt (fun w => a / (w - p) ^ 2) x0 x1 y0 y1 = 0 := by
  change PI.EF.Rect.rectInt (fun w => a / (w - p) ^ 2) ⟨x0, y0⟩ ⟨x1, y1⟩ = _
  have hin : p ∈ PI.EF.Rect.rectOpen ⟨x0, y0⟩ ⟨x1, y1⟩ := ⟨h1, h2, h3, h4⟩
  rw [PI.EF.Rect.rectInt_div_sub_sq hin (differentiableOn_const a), deriv_const, mul_zero]

theorem rdp_seg (g G : ℂ → ℂ) (a b p : ℂ) (γ : ℝ → ℂ) (s t : ℝ) (hγ : Continuous γ)
    (hG : ContinuousOn (fun u => G (γ u)) (Set.uIcc s t)) (hP : ∀ u ∈ Set.uIcc s t, γ u ≠ p)
    (hg : ∀ w : ℂ, w ≠ p → g w = G w + a / (w - p) ^ 2 + b / (w - p)) :
    IntervalIntegrable (fun u => g (γ u) - a / (γ u - p) ^ 2) MeasureTheory.volume s t ∧
    IntervalIntegrable (fun u => a / (γ u - p) ^ 2) MeasureTheory.volume s t := by
  have hD : ContinuousOn (fun u => a / (γ u - p) ^ 2) (Set.uIcc s t) := by
    refine ContinuousOn.div₀ continuousOn_const (by fun_prop) (fun u hu => ?_)
    exact pow_ne_zero _ (sub_ne_zero.2 (hP u hu))
  have hS : ContinuousOn (fun u => G (γ u) + b / (γ u - p)) (Set.uIcc s t) := by
    refine hG.add (ContinuousOn.div₀ continuousOn_const (by fun_prop) (fun u hu => ?_))
    exact sub_ne_zero.2 (hP u hu)
  refine ⟨(hS.congr fun u hu => ?_).intervalIntegrable, hD.intervalIntegrable⟩
  rw [hg _ (hP u hu)]
  ring

theorem rectangle_double_pole : RectDoublePole := by
  intro g G a b p x0 x1 y0 y1 h1 h2 h3 h4 hU hg
  obtain ⟨U, -, hsub, hG⟩ := hU
  let z : ℂ := ⟨x0, y0⟩
  let w : ℂ := ⟨x1, y1⟩
  have hx := h1.trans h2
  have hy := h3.trans h4
  have hin : p ∈ PI.EF.Rect.rectOpen z w := ⟨h1, h2, h3, h4⟩
  have hD : DifferentiableOn ℂ G (PI.EF.Rect.rectClosed z w) := hG.mono (by
    rw [Set.uIcc_of_le hx.le, Set.uIcc_of_le hy.le] at hsub
    exact hsub)
  have hC := hD.continuousOn.mono (PI.EF.Rect.rectBdry_subset hx.le hy.le)
  have hA := PI.EF.Rect.continuousOn_div_sub_sq (h := fun _ => a) hin continuousOn_const
  have hB := PI.EF.Rect.continuousOn_div_sub (h := fun _ => b) hin continuousOn_const
  have hGA : ContinuousOn (fun s => G s + a / (s - p) ^ 2) (PI.EF.Rect.rectBdry z w) := hC.add hA
  have hEq : Set.EqOn g (fun s => G s + a / (s - p) ^ 2 + b / (s - p)) (PI.EF.Rect.rectBdry z w) :=
    fun s hs => hg s (PI.EF.Rect.ne_of_mem_bdry_of_mem_open hs hin)
  have hzero : PI.EF.Rect.rectInt G z w = 0 :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn G z w (hG.mono hsub)
  change PI.EF.Rect.rectInt g z w = _
  rw [PI.EF.Rect.rectInt_congr hEq, PI.EF.Rect.rectInt_add hGA hB, PI.EF.Rect.rectInt_add hC hA,
    hzero, PI.EF.Rect.rectInt_div_sub_sq hin (differentiableOn_const a),
    PI.EF.Rect.rectInt_div_sub hin (differentiableOn_const b),
    deriv_const, mul_zero, zero_add, zero_add]

end Formalism.ZF
