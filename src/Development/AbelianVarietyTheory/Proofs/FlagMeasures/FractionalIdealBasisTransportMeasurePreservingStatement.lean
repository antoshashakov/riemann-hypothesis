module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FractionalIdealBasisTransportMeasurePreserving
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

theorem _root_.GlobalTheory.T.fractionalIdeal_basis_transport_measurePreserving : ∀ (K : Type) [Field K] [NumberField K] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure W) (e : mixedEmbedding.mixedSpace K ≃L[ℝ] W), MeasurePreserving e volume μ → ∀ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ W), (Submodule.span ℤ (Set.range b) : Set W) = (fun x : K => e (mixedEmbedding K x)) '' {x : K | x ∈ (J : FractionalIdeal (𝓞 K)⁰ K)} ∧ μ (ZSpan.fundamentalDomain b) = ENNReal.ofReal (FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K) * (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|) := by
  first | exact @GlobalTheory.SnMass.VolN.fractionalIdeal_basis_transport | exact GlobalTheory.SnMass.VolN.fractionalIdeal_basis_transport | (intros; apply GlobalTheory.SnMass.VolN.fractionalIdeal_basis_transport <;> assumption)
