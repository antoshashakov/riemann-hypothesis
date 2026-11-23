module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndEnc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Rt0ConjNegNeZero

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  first
  | exact @_root_.UpperTheory.Reformulated.B.Ga10.rt0_conj_neg_ne_zero
  | exact _root_.UpperTheory.Reformulated.B.Ga10.rt0_conj_neg_ne_zero
  | (apply _root_.UpperTheory.Reformulated.B.Ga10.rt0_conj_neg_ne_zero <;> assumption)
  | (intros; apply _root_.UpperTheory.Reformulated.B.Ga10.rt0_conj_neg_ne_zero <;> assumption)
  | (intros; apply @_root_.UpperTheory.Reformulated.B.Ga10.rt0_conj_neg_ne_zero <;> first | assumption | infer_instance)
  | (intros; exact _root_.UpperTheory.Reformulated.B.Ga10.rt0_conj_neg_ne_zero ..)

theorem psiCover_holds (H : Host E) : PsiCoverSt H := by
  intro τ
  have hsq : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have e : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa using this
    rw [← map_pow, e]
    simp
  have hpm : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
    have h : (τ (H.rt : E) - H.rt0) * (τ (H.rt : E) + H.rt0) = 0 := by
      have e : (τ (H.rt : E) - H.rt0) * (τ (H.rt : E) + H.rt0) = τ (H.rt : E) ^ 2 - H.rt0 ^ 2 := by ring
      rw [e, hsq, H.sqrt_neg_disc_sq, sub_self]
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hpm with h | h
  · exact Or.inl h
  · right
    show starRingEnd ℂ (τ (H.rt : E)) = H.rt0
    rw [h, map_neg, rt0_conj_neg_ne_zero, neg_neg]

end Formalism.MainNotions.ModuliIntegralCharts.H1
