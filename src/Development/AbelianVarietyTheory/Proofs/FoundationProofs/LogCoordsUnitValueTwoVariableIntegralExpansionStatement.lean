module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvOfFintype
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesAndDerivUniqueOfCoefficientsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesCongIffCoeffAndIsUnitStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDlog
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntPrimeDivRootOfUnitySubOnePowStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogCoordsUnitValueTwoVariableIntegralExpansion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelEmbeddingInjectiveRangeAdjoinRootsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgZpOfPow

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.logCoords_unit_value_twoVariableIntegralExpansion : ∀ (p : ℕ) [Fact p.Prime] (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (T : GlobalTheory.K5.Tower p Ωl) (L : ℕ) (ψ : O0 p →+* Ωl) (ι : On p L →ₐ[O0 p] Ωl), 1 ≤ L → IsReb T L ψ → IsEmb T L ι →
  ∀ (A₁ g : ℤ) (θ : ℤ → ℤ → ℤ) (cU cE : ℤ → Ωl) (x x' : Ωl),
  (∀ r : ℤ, ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k r = 0) →
  (∃ r0 : ℤ, ∀ k r : ℤ, r < r0 → θ k r = 0) →
  (∀ k r : ℤ, θ k r ≠ 0 → (p : ℤ) ^ L ∣ r - A₁ * k) →
  (∀ r : ℤ, cU r = ∑ᶠ k : ℤ, (θ k r : Ωl) * T.ζ L ^ (g * k)) →
  (∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ωl) * T.ζ L ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i)) →
  (∀ r : ℤ, r < 0 → cE r = 0) → (∀ r : ℤ, cE r ∈ Subring.closure {T.ζ L}) →
  Ev ψ cU x x' → x ≠ 0 → IsInt (p := p) x⁻¹ →
  ∃ (w : (On p L)ˣ) (α β : On p L) (z z' : Ωl), IsDlog p L (w : On p L) α β ∧ ι w = x ∧ Ev ψ cE z z' ∧
    Cong (p := p) L (ι α) (-(A₁ : Ωl) * z) ∧
    Cong (p := p) L ((p : Ωl) * ι β) (-(p : Ωl) * (g : Ωl) * z) := by
  exact _root_.GlobalTheory.Glue.SiegLoc.local_coords
