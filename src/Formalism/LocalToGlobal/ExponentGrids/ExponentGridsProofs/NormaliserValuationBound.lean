module

public import Formalism.QuotientMetricDivisors.Statement
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.QuotientMetricDivisors.Complement2Normaliser
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondComplementParameterBounds
public import Formalism.TranslateCocycles.StatementHC

@[expose] public section

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl lw PlOver IsConjAt)
open Formalism.CG (HCdeg HCDplus HCDminus)

noncomputable section

namespace Formalism.AtG

namespace ValuationJets

open Formalism.DivisionValues.ValuationRepresentative Formalism.DivisionValues.PlaceSumConjugation

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem val_int (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    w.valuation K (x : K) = WithZero.exp (-(vw w (x : K))) := by
  rw [show (x : K) = algebraMap (𝓞 K) K x from rfl,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg _ hx]
  congr 1
  rw [neg_inj]
  unfold vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w (by simpa using hx)]

theorem val_eq (w : HeightOneSpectrum (𝓞 K)) (a : K) (ha : a ≠ 0) :
    w.valuation K a = WithZero.exp (-(vw w a)) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have hy0 : algebraMap (𝓞 K) K y ≠ 0 := (div_ne_zero_iff.mp ha).2
  have hx : x ≠ 0 := fun h => ha (by simp [h])
  have vx := val_int w x hx
  have vy := val_int w y (nonZeroDivisors.ne_zero hy)
  rw [show ((x : K)) = algebraMap (𝓞 K) K x from rfl] at vx
  rw [show ((y : K)) = algebraMap (𝓞 K) K y from rfl] at vy
  have hmul : vw w (algebraMap (𝓞 K) K x) =
      vw w (algebraMap (𝓞 K) K x / algebraMap (𝓞 K) K y) + vw w (algebraMap (𝓞 K) K y) := by
    rw [← vw_mul w _ _ ha hy0, div_mul_cancel₀ _ hy0]
  rw [map_div₀, vx, vy, ← WithZero.exp_sub]
  congr 1
  linarith

theorem vw_add (w : HeightOneSpectrum (𝓞 K)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    min (vw w a) (vw w b) ≤ vw w (a + b) := by
  have h1 := (w.valuation K).map_add a b
  rw [val_eq w a ha, val_eq w b hb, val_eq w _ hab] at h1
  rcases le_max_iff.mp h1 with h | h
  · exact le_trans (min_le_left _ _) (neg_le_neg_iff.mp (WithZero.exp_le_exp.mp h))
  · exact le_trans (min_le_right _ _) (neg_le_neg_iff.mp (WithZero.exp_le_exp.mp h))


end ValuationJets

open ValuationJets Formalism.DivisionValues.ValuationRepresentative Formalism.DivisionValues.PlaceSumConjugation

end Formalism.AtG
