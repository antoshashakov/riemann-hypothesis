module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualFamilyIsBasisStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOfSmoothStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalenceStatement
public import Development.WeilBound.CoreStatements.SesquilinearFractions.GLieInt
import Development.WeilBound.CoreStatements.SesquilinearFractions.GLieIntA
import Development.WeilBound.CoreStatements.SesquilinearFractions.GLieIntC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

open PositivityTheory.Xgf.isogeny_decomposition_product in

theorem _root_.GlobalTheory.CompanionTheory.Relay.isogeny_decomposition_product : ∀ (R V : Type) [CommRing R] [CommRing V] [IsLocalRing V] (f : R →+* V) (n N : ℕ) (C : Fin n → Out.PolAV (Sp R)) (v : ∀ k, epsR R ⟶ (C k).A) (B : Out.PolAV (Sp R)) (ψ : ∀ k, (C k).A ⟶ B.A) (χ : ∀ k, B.A ⟶ (C k).A) (G : Over (Sp V)) [GrpObj G] (π : G.left ⟶ B.A.left), B.g = n → (∀ k, IsLieBasis ![v k]) → (∀ k, IsMonHom (ψ k)) → (∀ k, IsMonHom (χ k)) → (∀ k, ψ k ≫ χ k = 𝟙 (C k).A ^ N) → (∀ k k', k ≠ k' → ψ k ≫ χ k' = 1) → IsUnit (N : V) → IsGrpPullback G B.A (spMap f) π → ∃ u : Fin n → (epsAt (𝟙 (Sp V)) ⟶ G), (∀ k, (u k).left ≫ π = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left) ∧ (∀ k, IsTanAt G _ (u k)) ∧ ∀ w, IsTanAt G _ w → ∃! cc : Fin n → V, IsComb cc u w := by
  exact PositivityTheory.Xgf.isogeny_decomposition_product
