module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PullCochMemCoboundaries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechShortExactPullCompat
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

theorem _root_.GlobalTheory.T.cech_short_exact_pull_compat : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) {F I Q : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {F' I' Q' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} {g₁ : F ⟶ I} {g₂ : I ⟶ Q} {g₁' : F' ⟶ I'} {g₂' : I' ⟶ Q'}
    (hC : IsCechShortExact V g₁ g₂) (hC' : IsCechShortExact U g₁' g₂') (φ₁ : F ⟶ (Opens.map f).op ⋙ F')
    (φ₂ : I ⟶ (Opens.map f).op ⋙ I') (φ₃ : Q ⟶ (Opens.map f).op ⋙ Q')
    (h₁₂ : ∀ W x, φ₂.app W (g₁.app W x) = g₁'.app _ (φ₁.app W x))
    (h₂₃ : ∀ W x, φ₃.app W (g₂.app W x) = g₂'.app _ (φ₂.app W x)) (n : ℕ) (σ : cocycles Q V n),
    cechPullH f φ₁ V U τ hτ (n + 1) (hC.delta n σ) =
      hC'.delta n ⟨pullCoch f φ₃ V U τ hτ n σ.1, pullCoch_mem_cocycles f φ₃ V U τ hτ σ.2⟩ := by
        exact GlobalTheory.CompanionTheory.OmCechDelta.cechPullH_delta
