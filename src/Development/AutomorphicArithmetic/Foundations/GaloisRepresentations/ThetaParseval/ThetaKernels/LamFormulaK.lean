module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DCdE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTransformEqOrientedThetaFunctionCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsStdCharFOfIsGoodK
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LamFormula
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.AdelicSchwartzProperties
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem lam_formula_k {σ : E →ₐ[F] E} {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (hν : ν.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) (N : ℕ)
    (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N)
    (hCe : ∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u))
    (he : ∀ w w', symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w w' = symV (e w) (e w'))
    (hβc : Continuous β) (hβs : Continuous β.symm)
    (hr1 : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y : Fin N → F, β (ratWF x) = GlobalTheory.SWQ.rat y)
    (hr2 : ∀ y : Fin N → F, ∃ x : Matrix (Fin nT) (Fin nS) E, β (ratWF x) = GlobalTheory.SWQ.rat y) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F (Fin N), ∀ v : WOF F E nS nT,
      GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
        (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dCd F JT * v) (thV B.ψ Φ ∘ e)) =
        c * Φ (α v) :=
  _root_.PositivityTheory.ThKW.AdelicSchwartzProperties.lam_formula_c hB.cm hB.std JS JT ξ₀ ν 𝓕 hν h𝓕 N α β e hCe he hβc hβs hr1 hr2
end PositivityTheory.ThKW.AdelicSchwartzProperties
end
end
