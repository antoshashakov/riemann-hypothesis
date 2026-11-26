module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAddCharSymplecticSelfPairingPlaceCoordStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAtStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharLocalComponentNeOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGeneratoStatement
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsFinitePlaceVacuumAnyDarbouxCoordinates

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacAny

private theorem supported_sum {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {ι : Type} (s : Finset ι) {f : ι → AF F}
    (h : ∀ i ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (f i)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (∑ i ∈ s, f i) := by
  intro u hu
  rw [Finset.smul_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi u hu

private theorem supported_neg {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {x : AF F}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (-x) := by
  intro u hu
  rw [smul_neg, h u hu, neg_zero]

private theorem supported_atPlace {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} (t : Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (GlobalTheory.EmbChart.atPlace v t) := by
  intro u hu
  rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]

private theorem supported_mul_right {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {x : AF F}
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x) (y : AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x * y) := by
  intro u hu
  rw [smul_eq_mul, ← mul_assoc, show u * x = 0 from hx u hu, zero_mul]

private theorem supported_mul_left {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} (x : AF F) {y : AF F}
    (hy : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) y) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x * y) := by
  rw [mul_comm]
  exact supported_mul_right hy x

private theorem supported_sub {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {x y : AF F}
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x)
    (hy : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) y) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x - y) := by
  intro u hu
  rw [smul_sub, hx u hu, hy u hu, sub_self]

private theorem evFin_invOf_two_local {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} :
    GlobalTheory.AdelicU.evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
  refine (invOf_eq_right_inv ?_).symm
  have h : GlobalTheory.AdelicU.evFin F v (2 * ⅟(2 : AF F)) = 1 := by
    rw [mul_invOf_self, map_one]
  rwa [map_mul, map_ofNat] at h

theorem exists_isVac_any_darboux : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d)) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ φ, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v φ :=
  Tw.VacAny.exists_isVac_any_darboux

end GlobalTheory.VacAny
