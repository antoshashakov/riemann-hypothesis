module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralUnfoldSumTransitiveOrbit
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.lintegral_unfold_sum_transitive_orbit : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y] [MulAction Γ Y] (y₀ : Y), (∀ y, ∃ γ : Γ, γ • y₀ = y) → ∀ (𝓕 𝓖 : Set H), IsFundamentalDomain Γ 𝓕 ν → IsFundamentalDomain ((MulAction.stabilizer Γ y₀).map Γ.subtype) 𝓖 ν → ∀ Φ : Y → H → ℂ, (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) → (∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν) ∧ (∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν ≠ ⊤ → ∫ h in 𝓖, Φ y₀ h ∂ν = ∫ h in 𝓕, ∑' y, Φ y h ∂ν) := by
  first | exact @GlobalTheory.Unf.lintegral_integral_unfold_transitive | exact GlobalTheory.Unf.lintegral_integral_unfold_transitive | (intros; apply GlobalTheory.Unf.lintegral_integral_unfold_transitive <;> assumption)
