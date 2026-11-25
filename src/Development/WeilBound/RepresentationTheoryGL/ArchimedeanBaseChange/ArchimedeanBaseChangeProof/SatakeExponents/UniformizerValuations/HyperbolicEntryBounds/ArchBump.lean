module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Development.DiscreteGroups.PiInvariants.CasimirInfinity.CasInfOfIm

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



namespace PositivityTheory.Rg.BcB.F.F0

open PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA

theorem cosh_im_zero (c : ℂ) (hc : c.im = 0) (t : ℝ) : (Complex.cosh (t * c ^ (1 / 2 : ℂ))).im = 0 := by
  set s := c ^ (1 / 2 : ℂ) with hs
  have hsq : s ^ 2 = c := by
    have := Complex.cpow_nat_inv_pow c (n := 2) (by norm_num)
    simpa [hs, one_div] using this
  have him : s.re * s.im = 0 := by
    have h := congrArg Complex.im hsq
    rw [hc, pow_two, Complex.mul_im] at h
    linarith
  rcases mul_eq_zero.1 him with h | h
  · have e : (t : ℂ) * s = ((t * s.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [h]
    rw [e, Complex.cosh_mul_I, ← Complex.ofReal_cos, Complex.ofReal_im]
  · have e : (t : ℂ) * s = ((t * s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [h]
    rw [e, ← Complex.ofReal_cosh, Complex.ofReal_im]

theorem bump_one' (ι : Type) [Fintype ι] (c : ι → ℂ) (hc : ∀ i, (c i).im = 0) :
    ∃ (g : ℝ → ℝ) (T : ℝ), 0 ≤ T ∧ IsBump g T ∧ ∏ i, coshT g (c i) = 1 :=
  PositivityTheory.Rg.BcB.F.F0.bump_one ι c hc

end PositivityTheory.Rg.BcB.F.F0

end
