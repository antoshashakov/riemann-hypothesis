module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CompanionTheory.ChartAlg in

theorem _root_.GlobalTheory.T.exists_chart_from_coordinates : ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {I : Ideal R} (γ : DividedPowers I) (l s : ℕ)
    (hb : TFBase γ l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I)
    (hκ : ∀ a, κ a = Ideal.Quotient.mk I (algebraMap O R a)) {V : X.Opens} {d : ℕ} (c : Coord q V d),
    letI := (strV q V).toAlgebra
    ∃ (c' : Chart γ 0 q κ V d) (e : R ⊗[O] Γ(X, V) ≃+* c'.D.B), TF l s c'.D ∧ (∀ r, e (r ⊗ₜ 1) = c'.D.i r) ∧
      (∀ i, e (1 ⊗ₜ c.t i) = c'.t i) ∧ ∀ f, ev c'.D c'.inV f = Ideal.Quotient.mk _ (e (1 ⊗ₜ f)) := by
        exact GlobalTheory.CompanionTheory.ChartAlg.chart_exists
