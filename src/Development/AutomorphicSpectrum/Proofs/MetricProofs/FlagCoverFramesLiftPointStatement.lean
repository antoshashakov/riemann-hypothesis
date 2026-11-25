module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CoordinateRatioValueAtPointStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointMapsToPointsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointRegular
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesLiftPoint
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesPullbackStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPointsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBlockDiagMapGenBlock
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph GlobalTheory.CompanionTheory.Ar.PB.CovGraph.BStep

theorem _root_.GlobalTheory.T.flag_cover_frames_lift_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z₁ : (Σ k, ι' k) → ℂ) (z₀ : (Σ k, ι k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) (k : K), z₁ ∈ mcPts (mCoordIdeal y') → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z₁ ∘ Cv.v)) → M'.IsFlagOf F' z₁ h → M.IsFlagOf F z₀ (fun τ => Cv.trans F' F (basePart M'.blk z₁) τ * h τ) → SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) → M.blk p = some k → ∃ (e : Φ') (s : ι k → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ m, transPt Cv ⟨k, m⟩ = e * s m ∧ IsValueAt y' (s m) z₁ (t * z₀ ⟨k, m⟩) := by
  exact _root_.GlobalTheory.CompanionTheory.Ar.PB.CovGraph.BStep.main
