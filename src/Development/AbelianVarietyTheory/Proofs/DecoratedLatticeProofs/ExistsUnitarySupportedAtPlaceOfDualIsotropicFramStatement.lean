module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitarySupportedAtPlaceOfDualIsotropicFram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open GlobalTheory.IwaPlace.BuildQ in

theorem _root_.GlobalTheory.T.exists_unitarySupportedAtPlace_of_dual_isotropic_frames : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (α β : Fin ρ → AE D) (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i, α i ∈ idAt D (· = v)) → (∀ i, β i ∈ idAt D (· = v)) → (∀ i, α i * β i = ε) → (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i j, c' i j ∈ idAt D (· = v)) → adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) → adj c' * (gA S * c') = 0 → ∃ q ∈ grpAt S (· = v), mt S q * d.jX = d.jX * (b * Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)) ∧ (∀ i, mt S q *ᵥ colMul d.jX i (α i) = fun k => (d.jX * b) k i) ∧ (∀ i, mt S q *ᵥ colMul d.jY i (cA D (β i)) = fun k => c' k i) := by
  exact GlobalTheory.IwaPlace.exists_grpAt_of_dual_frames
