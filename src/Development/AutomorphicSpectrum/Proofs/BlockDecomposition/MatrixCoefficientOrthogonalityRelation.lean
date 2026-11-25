module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulInner
public import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.UnitaryMatrixCoefficientDecay
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityUnfoldSubgroup

@[expose] public section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeA

theorem isInvInvariant_of_right_haar {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant :=
  GlobalTheory.GenUnfold.isInvInvariant μ

theorem isSelfAdjoint_coefOp : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (hσ : IsU σ), IsU ρ → ∀ (v : B) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν),
    IsSelfAdjoint (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ hσ hρ v hm
  haveI := GlobalTheory.CompanionTheory.RgHeA.isInvInvariant_of_right_haar ν
  obtain ⟨_, hadj, _, _⟩ := PositivityTheory.UnitaryDecomposition.X4.uRep_of hσ
  obtain ⟨_, hρadj, _, _⟩ := PositivityTheory.UnitaryDecomposition.X4.uRep_of hρ
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro a b
  try simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, GlobalTheory.CompanionTheory.RgHeA.inner_coefOp, GlobalTheory.CompanionTheory.RgHeA.inner_coefOp, ← integral_conj]
  calc ∫ g, (starRingEnd ℂ) (star ⟪v, ρ g v⟫_ℂ * ⟪b, σ g a⟫_ℂ) ∂ν
      = ∫ g, star ⟪v, ρ g⁻¹ v⟫_ℂ * ⟪a, σ g⁻¹ b⟫_ℂ ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        have e1 : star ⟪v, ρ g⁻¹ v⟫_ℂ = ⟪v, ρ g v⟫_ℂ := by
          rw [← hρadj]
          exact inner_conj_symm _ _
        have e2 : (starRingEnd ℂ) ⟪b, σ g a⟫_ℂ = ⟪a, σ g⁻¹ b⟫_ℂ := by
          rw [inner_conj_symm, hadj]
        show (starRingEnd ℂ) (star ⟪v, ρ g v⟫_ℂ * ⟪b, σ g a⟫_ℂ) = star ⟪v, ρ g⁻¹ v⟫_ℂ * ⟪a, σ g⁻¹ b⟫_ℂ
        rw [map_mul, e1, e2, starRingEnd_apply, star_star]
    _ = ∫ g, star ⟪v, ρ g v⟫_ℂ * ⟪a, σ g b⟫_ℂ ∂ν :=
        integral_inv_eq_self (fun g => star ⟪v, ρ g v⟫_ℂ * ⟪a, σ g b⟫_ℂ) ν

end GlobalTheory.CompanionTheory.RgHeA
