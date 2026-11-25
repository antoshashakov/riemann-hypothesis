module

public import Formalism.LFunctionBounds.ExpSumLowerBound
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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

import
  Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.RectIntEqZeroOfDifferentiableOn

@[expose] public section

open Complex

noncomputable section

namespace Formalism.FX

theorem rectRes_ftc_log {γ : ℝ → ℂ} {d : ℂ} {a b : ℝ} (hγ : ∀ t, HasDerivAt γ d t)
    (hs : ∀ t ∈ Set.uIcc a b, γ t ∈ slitPlane) :
    ∫ t in a..b, d / γ t = log (γ b) - log (γ a) := by
  have hc : Continuous γ := continuous_iff_continuousAt.2 fun t => (hγ t).continuousAt
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => (hγ t).clog_real (hs t ht)) ?_
  refine ContinuousOn.intervalIntegrable ?_
  exact continuousOn_const.div hc.continuousOn fun t ht => Complex.slitPlane_ne_zero (hs t ht)

theorem rectRes_log_sub_log_neg_of_im_pos {z : ℂ} (h : 0 < z.im) :
    log z - log (-z) = (Real.pi : ℂ) * I := by
  have h1 := Complex.arg_neg_eq_arg_sub_pi_of_im_pos h
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]

theorem rectRes_log_sub_log_neg_of_im_neg {z : ℂ} (h : z.im < 0) :
    log z - log (-z) = -((Real.pi : ℂ) * I) := by
  have h1 := Complex.arg_neg_eq_arg_add_pi_of_im_neg h
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]

theorem rectRes_hasDerivAt_horiz (c : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) + c) 1 t := by
  have h := (Complex.ofRealCLM.hasDerivAt (x := t)).add_const c
  simpa using h

theorem rectRes_hasDerivAt_vert (c : ℂ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => c + (y : ℂ) * I) I t := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add c
  simpa using h

theorem rectInt_inv_sub (p : ℂ) (x0 x1 y0 y1 : ℝ) (h1 : x0 < p.re) (h2 : p.re < x1)
    (h3 : y0 < p.im) (h4 : p.im < y1) :
    rectInt (fun w => 1 / (w - p)) x0 x1 y0 y1 = 2 * (Real.pi : ℂ) * I := by
  change PI.EF.Rect.rectInt (fun w => 1 / (w - p)) ⟨x0, y0⟩ ⟨x1, y1⟩ = _
  simpa only [one_div] using PI.EF.Rect.rectInt_inv_sub (p := p) (z := ⟨x0, y0⟩) (w := ⟨x1, y1⟩)
    ⟨h1, h2, h3, h4⟩

theorem rectRes_edge (g G : ℂ → ℂ) (P : Finset ℂ) (b : ℂ → ℂ) (γ : ℝ → ℂ) (a c : ℝ)
    (hγ : Continuous γ) (hG : ContinuousOn (fun t => G (γ t)) (Set.uIcc a c))
    (hP : ∀ t ∈ Set.uIcc a c, ∀ p ∈ P, γ t ≠ p)
    (hg : ∀ w : ℂ, w ∉ P → g w = G w + ∑ p ∈ P, b p / (w - p)) :
    ∫ t in a..c, g (γ t) =
      (∫ t in a..c, G (γ t)) + ∑ p ∈ P, b p * ∫ t in a..c, 1 / (γ t - p) := by
  have hγP : ∀ t ∈ Set.uIcc a c, γ t ∉ P := fun t ht hmem => hP t ht _ hmem rfl
  have hcont : ∀ p ∈ P, ContinuousOn (fun t => 1 / (γ t - p)) (Set.uIcc a c) := fun p hp =>
    continuousOn_const.div (hγ.continuousOn.sub continuousOn_const)
      (fun t ht => sub_ne_zero.2 (hP t ht p hp))
  calc ∫ t in a..c, g (γ t)
      = ∫ t in a..c, (G (γ t) + ∑ p ∈ P, b p * (1 / (γ t - p))) := by
        refine intervalIntegral.integral_congr (fun t ht => ?_)
        show g (γ t) = G (γ t) + ∑ p ∈ P, b p * (1 / (γ t - p))
        rw [hg _ (hγP t ht)]
        congr 1
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [mul_one_div]
    _ = (∫ t in a..c, G (γ t)) + ∫ t in a..c, ∑ p ∈ P, b p * (1 / (γ t - p)) := by
        refine intervalIntegral.integral_add hG.intervalIntegrable ?_
        exact (continuousOn_finsetSum P (fun p hp => continuousOn_const.mul (hcont p hp))).intervalIntegrable
    _ = (∫ t in a..c, G (γ t)) + ∑ p ∈ P, b p * ∫ t in a..c, 1 / (γ t - p) := by
        rw [intervalIntegral.integral_finsetSum]
        · simp_rw [intervalIntegral.integral_const_mul]
        · intro p hp
          exact ((hcont p hp).intervalIntegrable).const_mul (b p)

theorem rectRes_sum_combo (P : Finset ℂ) (b A B C D : ℂ → ℂ) :
    ∑ p ∈ P, b p * (A p - B p + I * C p - I * D p) =
      ∑ p ∈ P, b p * A p - ∑ p ∈ P, b p * B p + I * ∑ p ∈ P, b p * C p - I * ∑ p ∈ P, b p * D p := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem rectangle_residue : RectResidue := by
  intro g G P b x0 x1 y0 y1 hx hy hPin hU hg
  obtain ⟨U, -, hsub, hG⟩ := hU
  let z : ℂ := ⟨x0, y0⟩
  let w : ℂ := ⟨x1, y1⟩
  have hD : DifferentiableOn ℂ G (PI.EF.Rect.rectClosed z w) := hG.mono (by
    rw [Set.uIcc_of_le hx.le, Set.uIcc_of_le hy.le] at hsub
    exact hsub)
  have hin (p : ℂ) (hp : p ∈ P) : p ∈ PI.EF.Rect.rectOpen z w := hPin p hp
  have hC : ContinuousOn G (PI.EF.Rect.rectBdry z w) :=
    hD.continuousOn.mono (PI.EF.Rect.rectBdry_subset hx.le hy.le)
  have hB (p : ℂ) (hp : p ∈ P) :
      ContinuousOn (fun s => b p / (s - p)) (PI.EF.Rect.rectBdry z w) :=
    PI.EF.Rect.continuousOn_div_sub (hin p hp) continuousOn_const
  have hEq : Set.EqOn g (fun s => G s + ∑ p ∈ P, b p / (s - p)) (PI.EF.Rect.rectBdry z w) :=
    fun s hs => hg s fun hp => PI.EF.Rect.ne_of_mem_bdry_of_mem_open hs (hin s hp) rfl
  have hzero : PI.EF.Rect.rectInt G z w = 0 :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn G z w (hG.mono hsub)
  change PI.EF.Rect.rectInt g z w = _
  rw [PI.EF.Rect.rectInt_congr hEq, PI.EF.Rect.rectInt_add hC (continuousOn_finsetSum _ hB),
    hzero, zero_add, PI.EF.Rect.rectInt_finset_sum P _ hB, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p hp =>
    PI.EF.Rect.rectInt_div_sub (hin p hp) (differentiableOn_const (b p))

end Formalism.FX
