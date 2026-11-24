module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompletionTwistDataChainColumns
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
open GlobalTheory.TwBridgeInhab in

theorem _root_.GlobalTheory.T.exists_completionTwistData_chainColumns : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → ∀ (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl P.1 (qOf P.1) ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ ψ : AddChar k Circle, Continuous ψ → HasConductor ψ 1 → (∀ (a : X.E) (b : ℤ) (n : ℕ), IntAt P.1 (G.xi0 * a - (b : X.E) / (qOf P.1 : X.E) ^ n) → (ψ (ι a) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (qOf P.1 : ℂ) ^ n)) → ∀ μ : ℕ → kˣ →* ℂˣ, (∀ i, i < R.m → (∀ (a : X.E) (u : kˣ), (u : k) = ι a → (μ (i + 1) u : ℂ) = G.σ₀ (muAt Ch sel mu cst i P a)) ∧ IsTame (μ (i + 1))) → ∃ W : TwData k, AtTwist (R := R) sel mu cst G.σ₀ P ι s W ∧ W.ϖ = ϖ ∧ W.ψ = ψ ∧ (∀ i, i < R.m → W.η (i + 1) * W.δ = μ (i + 1)) ∧ (W.sg = 1 ∨ W.sg = -1) := by
  exact GlobalTheory.TwBridgeInhab.exists_twData
