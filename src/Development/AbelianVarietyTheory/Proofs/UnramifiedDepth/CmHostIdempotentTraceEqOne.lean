module

public import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity
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
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

@[expose] public section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.L2.FormalSeriesBounds NumberField

namespace GlobalTheory.QuadTrace

theorem bar_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.bar H.rt = -H.rt := by
  first
  | exact @_root_.GlobalTheory.HostModel.bar_rt
  | exact _root_.GlobalTheory.HostModel.bar_rt
  | (apply _root_.GlobalTheory.HostModel.bar_rt <;> assumption)
  | (intros; apply _root_.GlobalTheory.HostModel.bar_rt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.HostModel.bar_rt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.HostModel.bar_rt ..)

theorem cmHost_idempotent_trace_eq_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], Formalism.L2.FormalSeriesBounds.HostTraceIdentity H := by
  intro E _ _ _ H _ hstar
  rw [hstar]
  have hb := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add (f := _), map_one, bar_rt, map_ofNat] at hb
  have h2 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    linear_combination H.two_weight_eq_one_add_root + hb
  exact mul_left_cancel₀ two_ne_zero h2

end GlobalTheory.QuadTrace
