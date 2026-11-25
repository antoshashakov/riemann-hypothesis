module

public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuotientLatticeRealizedIsometrically
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.HermitianLattices.StatementLat

@[expose] public section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

theorem _root_.GlobalTheory.T.quotient_lattice_realized_isometrically : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (A S : Submodule (𝓞 K) (Fin n → K)), (∀ w, IsUnit (X w).det) → A.FG → IsSat (realize (Pi.basisFun K (Fin n)) X) A S → ∃ (m : ℕ) (q : Matrix (Fin m) (Fin n) K) (X' : InfinitePlace K → Matrix (Fin m) (Fin m) ℂ) (Q : InfinitePlace K → Matrix (Fin m) (Fin n) ℂ), m + rkK S = rkK A ∧ (∀ w, IsUnit (X' w).det) ∧ (∀ w, Q w * (Q w)ᴴ = 1) ∧ (∀ w, ∀ y ∈ A, fcoord (Pi.basisFun K (Fin m)) X' w (q *ᵥ y) = Q w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y) ∧ (∀ w z, (Q w)ᴴ *ᵥ z ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (A : Set (Fin n → K)))) ∧ (∀ w, ∀ u ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (A : Set (Fin n → K))), u - (Q w)ᴴ *ᵥ (Q w *ᵥ u) ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K)))) ∧ (∀ y ∈ S, q *ᵥ y = 0) ∧ Submodule.span K (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) : Set (Fin m → K)) = ⊤ ∧ ∀ N', N' ≤ A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) → N' ≠ ⊥ → ∃ N, S < N ∧ N ≤ A ∧ sizeQ (Pi.basisFun K (Fin n)) X N S = size (Pi.basisFun K (Fin m)) X' N' := by
  exact _root_.GlobalTheory.QuotCoord.quot_realized

