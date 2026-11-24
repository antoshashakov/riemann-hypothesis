module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.IdealNormPrincipalInExtension
import Supplements.MathlibImports.AnalysisAndTactics
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice

@[expose] public section

open NumberField GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.ideal_norm_principal_in_extension : ∀ (K : Type) [Field K] [NumberField K] (I : Ideal (𝓞 K)), I ≠ ⊥ → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (y : 𝓞 K'), y ≠ 0 ∧ y ∈ I.map (algebraMap (𝓞 K) (𝓞 K')) ∧ |((Algebra.norm ℚ (y : K') : ℚ) : ℝ)| = (I.absNorm : ℝ) ^ Module.finrank K K' := by
  first | exact @GlobalTheory.CompanionTheory.Lines.exists_principal_extension | exact GlobalTheory.CompanionTheory.Lines.exists_principal_extension | (intros; apply GlobalTheory.CompanionTheory.Lines.exists_principal_extension <;> assumption)
