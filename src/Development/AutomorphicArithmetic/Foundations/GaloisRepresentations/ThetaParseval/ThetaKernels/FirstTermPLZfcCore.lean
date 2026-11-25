module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.ArchimedeanJacquetFirstTerm.ArchimedeanWhittakerTrace.LZfcCore
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleAdaptedPlaneLocalFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
namespace PositivityTheory.FTA.ZFC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
variable {Y : Spc F E n}
theorem chr_ker_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b)
    (β : nA σ Y b) : (∀ T : nF σ Y b, chr B.ψ b T β = 1) ↔ β ∈ nF σ Y b :=
  _root_.PositivityTheory.FTA.ZFC.chr_ker_c hB.cm hB.std hb β
theorem fc_inj_pt_per_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (b : GL (Fin n ⊕ Fin n) E) (nb : nA σ Y b → G2 σ Y)
    (lam : Measure (nA σ Y b)) (𝓖 : Set (nA σ Y b)) (hb : IsFrame2 σ Y b) (hc : CoefData (σ := σ) (Y := Y) b nb lam 𝓖)
    (f : G2 σ Y → ℂ) (hf : Continuous f) (hper : ∀ β ∈ nF σ Y b, ∀ g, f (nb β * g) = f g) (x : G2 σ Y)
    (hx : ∀ T : nF σ Y b, fc B.ψ b nb lam 𝓖 f T x = 0) : f x = 0 :=
  _root_.PositivityTheory.FTA.ZFC.fc_inj_pt_per_c hB.cm hB.std b nb lam 𝓖 hb hc f hf hper x hx
end PositivityTheory.FTA.ZFC
end
end
